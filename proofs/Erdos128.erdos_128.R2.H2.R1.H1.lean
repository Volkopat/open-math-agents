import OMAReductions.R_Erdos128_erdos_128_R2_H2_R1

/-!
# Proof of Erdos128.erdos_128.R2.H2.R1.H1 (Brandt 1999 Grötzsch Containment Theorem)

Every non-3-colorable triangle-free graph G on n vertices with minimum degree δ(G) > n / 3
contains a homomorphic (in fact injective) copy of the 11-vertex Grötzsch graph.
-/

namespace OMA.E128Brandt.LPR

open Finset SimpleGraph

/- ### Part 1: Basic triangle-free and Property D_m helpers -/

lemma not_adj_both {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3) {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) :
    ¬ G.Adj y z :=
  fun hyz => OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hcf hxy hyz hxz

lemma prop_D {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (m : ℕ) (hm : 1 ≤ m) (xs : Fin (3 * m) → V) :
    ∃ y : V, m + 1 ≤ (Finset.univ.filter (fun i : Fin (3 * m) => G.Adj (xs i) y)).card := by
  have hsum_eq :
      ∑ y : V, (Finset.univ.filter (fun i : Fin (3 * m) => G.Adj (xs i) y)).card =
      ∑ i : Fin (3 * m), (G.neighborSet (xs i)).ncard := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← G.coe_neighborFinset, Set.ncard_coe_finset]
    have hc : (∑ y : V, if G.Adj (xs i) y then (1 : ℕ) else 0) =
        (Finset.univ.filter (fun y : V => G.Adj (xs i) y)).card := by
      rw [Finset.card_filter]
    rw [hc]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  have hgt : m * Fintype.card V < ∑ y : V, (Finset.univ.filter (fun i : Fin (3 * m) => G.Adj (xs i) y)).card := by
    rw [hsum_eq]
    have h3 : ∑ _i : Fin (3 * m), Fintype.card V < ∑ i : Fin (3 * m), 3 * (G.neighborSet (xs i)).ncard := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.card_pos.mp (by rw [Finset.card_univ, Fintype.card_fin]; omega)
      · intro i _; exact hmin (xs i)
    rw [← Finset.mul_sum] at h3
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
    nlinarith
  by_contra h
  push Not at h
  have hle : ∑ y : V, (Finset.univ.filter (fun i : Fin (3 * m) => G.Adj (xs i) y)).card ≤
      ∑ _y : V, m :=
    Finset.sum_le_sum fun y _ => by have := h y; omega
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  nlinarith

/- ### Part 2: Lemma 3.1 (Induced C_6 + D_2, D_3 + Maximal Triangle-Free => Grötzsch Υ) -/

lemma bool_toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

lemma c6_indep_ge_three (a1 a2 a3 b1 b2 b3 : Bool)
    (h12 : (!(a1 && b2)) = true) (h13 : (!(a1 && b3)) = true)
    (h21 : (!(a2 && b1)) = true) (h23 : (!(a2 && b3)) = true)
    (h31 : (!(a3 && b1)) = true) (h32 : (!(a3 && b2)) = true)
    (hsum : 3 ≤ a1.toNat + a2.toNat + a3.toNat + b1.toNat + b2.toNat + b3.toNat) :
    (a1 = true ∧ a2 = true ∧ a3 = true) ∨ (b1 = true ∧ b2 = true ∧ b3 = true) := by
  cases a1 <;> cases a2 <;> cases a3 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    first
    | exact Bool.noConfusion h12
    | exact Bool.noConfusion h13
    | exact Bool.noConfusion h21
    | exact Bool.noConfusion h23
    | exact Bool.noConfusion h31
    | exact Bool.noConfusion h32
    | (simp only [Bool.toNat_true, Bool.toNat_false] at hsum; omega)
    | decide

lemma bool_pair_le_one {a b : Bool} (h : (!(a && b)) = true) : a.toNat + b.toNat ≤ 1 := by
  cases a <;> cases b <;> first | decide | exact Bool.noConfusion h

lemma bool_zero_of_pair {a b : Bool} (hb : b = true) (h : (!(a && b)) = true) : a.toNat = 0 := by
  subst hb; cases a <;> first | decide | exact Bool.noConfusion h

lemma bool_zero_of_pair' {a : Bool} (h : (!(true && a)) = true) : a.toNat = 0 := by
  cases a <;> first | decide | exact Bool.noConfusion h

lemma bool_eq_false_of_toNat_zero {b : Bool} (h : b.toNat = 0) : b = false := by
  cases b <;> first | rfl | exact Nat.noConfusion h

lemma bool_eq_true_of_toNat_one {b : Bool} (h : b.toNat = 1) : b = true := by
  cases b <;> first | rfl | exact Nat.noConfusion h

lemma nine_indep_ge_four (a1 a2 a3 b1 b2 b3 c1 c2 c3 : Bool)
    (h12 : (!(a1 && b2)) = true) (h13 : (!(a1 && b3)) = true)
    (h21 : (!(a2 && b1)) = true) (h23 : (!(a2 && b3)) = true)
    (h31 : (!(a3 && b1)) = true) (h32 : (!(a3 && b2)) = true)
    (ha1 : (!(a1 && c1)) = true) (ha2 : (!(a2 && c2)) = true) (ha3 : (!(a3 && c3)) = true)
    (hb1 : (!(b1 && c1)) = true) (hb2 : (!(b2 && c2)) = true) (hb3 : (!(b3 && c3)) = true)
    (hsum : 4 ≤ a1.toNat + a2.toNat + a3.toNat + b1.toNat + b2.toNat + b3.toNat +
                c1.toNat + c2.toNat + c3.toNat) :
    (a1 = true ∧ b1 = true ∧ c2 = true ∧ c3 = true) ∨
    (a2 = true ∧ b2 = true ∧ c1 = true ∧ c3 = true) ∨
    (a3 = true ∧ b3 = true ∧ c1 = true ∧ c2 = true) := by
  have p1 := bool_pair_le_one ha1; have p2 := bool_pair_le_one ha2; have p3 := bool_pair_le_one ha3
  have q1 := bool_pair_le_one hb1; have q2 := bool_pair_le_one hb2; have q3 := bool_pair_le_one hb3
  have ba1 := bool_toNat_le_one a1; have ba2 := bool_toNat_le_one a2; have ba3 := bool_toNat_le_one a3
  have bb1 := bool_toNat_le_one b1; have bb2 := bool_toNat_le_one b2; have bb3 := bool_toNat_le_one b3
  have bc1 := bool_toNat_le_one c1; have bc2 := bool_toNat_le_one c2; have bc3 := bool_toNat_le_one c3
  have ha_any : a1 = true ∨ a2 = true ∨ a3 = true := by
    cases a1 <;> cases a2 <;> cases a3
    · simp only [Bool.toNat_false] at hsum; omega
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  have hb_any : b1 = true ∨ b2 = true ∨ b3 = true := by
    cases b1 <;> cases b2 <;> cases b3
    · simp only [Bool.toNat_false] at hsum; omega
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  rcases ha_any with ea | ea | ea <;> rcases hb_any with eb | eb | eb
  · left
    have z2 := bool_zero_of_pair eb h21; have z3 := bool_zero_of_pair eb h31
    have zb2 : b2.toNat = 0 := by subst ea; cases b2 <;> first | decide | exact Bool.noConfusion h12
    have zb3 : b3.toNat = 0 := by subst ea; cases b3 <;> first | decide | exact Bool.noConfusion h13
    have zc1 : c1.toNat = 0 := by subst ea; cases c1 <;> first | decide | exact Bool.noConfusion ha1
    rw [ea, eb] at hsum; simp only [Bool.toNat_true] at hsum
    exact ⟨ea, eb, bool_eq_true_of_toNat_one (by omega), bool_eq_true_of_toNat_one (by omega)⟩
  · subst ea; subst eb; exact Bool.noConfusion h12
  · subst ea; subst eb; exact Bool.noConfusion h13
  · subst ea; subst eb; exact Bool.noConfusion h21
  · right; left
    have z1 := bool_zero_of_pair eb h12; have z3 := bool_zero_of_pair eb h32
    have zb1 : b1.toNat = 0 := by subst ea; cases b1 <;> first | decide | exact Bool.noConfusion h21
    have zb3 : b3.toNat = 0 := by subst ea; cases b3 <;> first | decide | exact Bool.noConfusion h23
    have zc2 : c2.toNat = 0 := by subst ea; cases c2 <;> first | decide | exact Bool.noConfusion ha2
    rw [ea, eb] at hsum; simp only [Bool.toNat_true] at hsum
    exact ⟨ea, eb, bool_eq_true_of_toNat_one (by omega), bool_eq_true_of_toNat_one (by omega)⟩
  · subst ea; subst eb; exact Bool.noConfusion h23
  · subst ea; subst eb; exact Bool.noConfusion h31
  · subst ea; subst eb; exact Bool.noConfusion h32
  · right; right
    have z1 := bool_zero_of_pair eb h13; have z2 := bool_zero_of_pair eb h23
    have zb1 : b1.toNat = 0 := by subst ea; cases b1 <;> first | decide | exact Bool.noConfusion h31
    have zb2 : b2.toNat = 0 := by subst ea; cases b2 <;> first | decide | exact Bool.noConfusion h32
    have zc3 : c3.toNat = 0 := by subst ea; cases c3 <;> first | decide | exact Bool.noConfusion ha3
    rw [ea, eb] at hsum; simp only [Bool.toNat_true] at hsum
    exact ⟨ea, eb, bool_eq_true_of_toNat_one (by omega), bool_eq_true_of_toNat_one (by omega)⟩

lemma not_and_decide {p q : Prop} [Decidable p] [Decidable q] (h : p → q → False) :
    (!(decide p && decide q)) = true := by
  by_cases hp : p <;> by_cases hq : q
  · exact (h hp hq).elim
  · rw [decide_eq_true hp, decide_eq_false hq]; rfl
  · rw [decide_eq_false hp, decide_eq_true hq]; rfl
  · rw [decide_eq_false hp, decide_eq_false hq]; rfl

lemma card_filter_fin6 {p : Fin 6 → Prop} [DecidablePred p] :
    (Finset.univ.filter p).card =
      (decide (p 0)).toNat + (decide (p 1)).toNat + (decide (p 2)).toNat +
      (decide (p 3)).toNat + (decide (p 4)).toNat + (decide (p 5)).toNat := by
  rw [Finset.card_filter, Fin.sum_univ_six]
  have h : ∀ q : Prop, [Decidable q] → (if q then (1 : ℕ) else 0) = (decide q).toNat := fun q _ => by
    by_cases hq : q
    · rw [if_pos hq, decide_eq_true hq]; rfl
    · rw [if_neg hq, decide_eq_false hq]; rfl
  simp only [h]

lemma card_filter_fin9 {p : Fin 9 → Prop} [DecidablePred p] :
    (Finset.univ.filter p).card =
      (decide (p 0)).toNat + (decide (p 1)).toNat + (decide (p 2)).toNat +
      (decide (p 3)).toNat + (decide (p 4)).toNat + (decide (p 5)).toNat +
      (decide (p 6)).toNat + (decide (p 7)).toNat + (decide (p 8)).toNat := by
  rw [Finset.card_filter]
  have hsum : ∀ f : Fin 9 → ℕ, ∑ i : Fin 9, f i =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := fun f => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_eight]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc]
    ring
  rw [hsum]
  have h : ∀ q : Prop, [Decidable q] → (if q then (1 : ℕ) else 0) = (decide q).toNat := fun q _ => by
    by_cases hq : q
    · rw [if_pos hq, decide_eq_true hq]; rfl
    · rw [if_neg hq, decide_eq_false hq]; rfl
  simp only [h]

lemma grotzsch_from_c6_step {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a1 a2 a3 b1 b2 b3 x : V)
    (h12 : G.Adj a1 b2) (h13 : G.Adj a1 b3)
    (h21 : G.Adj a2 b1) (h23 : G.Adj a2 b3)
    (h31 : G.Adj a3 b1) (h32 : G.Adj a3 b2)
    (hn1 : ¬ G.Adj a1 b1) (hn2 : ¬ G.Adj a2 b2) (hn3 : ¬ G.Adj a3 b3)
    (hx1 : G.Adj x b1) (hx2 : G.Adj x b2) (hx3 : G.Adj x b3) :
    ∃ (v u : Fin 5 → V) (w : V),
      ∀ i : Fin 5,
        G.Adj (v i) (v (i + 1)) ∧ G.Adj (u i) (v (i + 1)) ∧
        G.Adj (u i) (v (i + 4)) ∧ G.Adj w (u i) := by
  have hne1 : a1 ≠ b1 := fun h => by
    rw [h] at h12; exact not_adj_both hcf h31 h32 h12
  have hne2 : a2 ≠ b2 := fun h => by
    rw [h] at h23; exact not_adj_both hcf h12 h13 h23
  have hne3 : a3 ≠ b3 := fun h => by
    rw [h] at h31; exact not_adj_both hcf h23 h21 h31
  obtain ⟨c1, hc1a, hc1b⟩ := hmax a1 b1 hne1 hn1
  obtain ⟨c2, hc2a, hc2b⟩ := hmax a2 b2 hne2 hn2
  obtain ⟨c3, hc3a, hc3b⟩ := hmax a3 b3 hne3 hn3
  -- Helper: given an index permutation where c1' is adj to a1, b1, c2, c3, build Grötzsch
  have hbuild : ∀ (A1 A2 A3 B1 B2 B3 C1 C2 C3 : V),
      G.Adj A1 B2 → G.Adj A1 B3 → G.Adj A2 B1 → G.Adj A2 B3 → G.Adj A3 B1 → G.Adj A3 B2 →
      G.Adj x B1 → G.Adj x B2 → G.Adj x B3 →
      G.Adj C1 A1 → G.Adj C1 B1 → G.Adj C1 C2 → G.Adj C1 C3 →
      G.Adj C2 A2 → G.Adj C2 B2 → G.Adj C3 A3 → G.Adj C3 B3 →
      ∃ (v u : Fin 5 → V) (w : V),
        ∀ i : Fin 5,
          G.Adj (v i) (v (i + 1)) ∧ G.Adj (u i) (v (i + 1)) ∧
          G.Adj (u i) (v (i + 4)) ∧ G.Adj w (u i) := by
    intro A1 A2 A3 B1 B2 B3 C1 C2 C3
      e12 e13 e21 e23 e31 e32 ex1 ex2 ex3 ec1a ec1b ec12 ec13 ec2a ec2b ec3a ec3b
    -- Apply D_2 to hexagon A2 - C2 - B2 - A3 - C3 - B3 - A2
    let xs6 : Fin 6 → V := fun i => match i.val with
      | 0 => A2 | 1 => B2 | 2 => C3 | 3 => A3 | 4 => B3 | _ => C2
    obtain ⟨q, hq⟩ := prop_D G hmin 2 (by omega) xs6
    rw [card_filter_fin6] at hq
    have hcls := c6_indep_ge_three
      (decide (G.Adj A2 q)) (decide (G.Adj B2 q)) (decide (G.Adj C3 q))
      (decide (G.Adj A3 q)) (decide (G.Adj B3 q)) (decide (G.Adj C2 q))
      (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e23)
      (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm ec2a.symm)
      (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e32.symm)
      (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm ec2b.symm)
      (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm ec3a)
      (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm ec3b)
      hq
    rcases hcls with ⟨hqA2, hqB2, hqC3⟩ | ⟨hqA3, hqB3, hqC2⟩
    · have qA2 : G.Adj q A2 := (of_decide_eq_true hqA2).symm
      have qB2 : G.Adj q B2 := (of_decide_eq_true hqB2).symm
      have qC3 : G.Adj q C3 := (of_decide_eq_true hqC3).symm
      refine ⟨![B1, A2, B3, C3, C1], ![C2, x, q, A1, A3], B2, fun i => ?_⟩
      fin_cases i
      · exact ⟨e21.symm, ec2a, ec12.symm, ec2b.symm⟩
      · exact ⟨e23, ex3, ex1, ex2.symm⟩
      · exact ⟨ec3b.symm, qC3, qA2, qB2.symm⟩
      · exact ⟨ec13.symm, ec1a.symm, e13, e12.symm⟩
      · exact ⟨ec1b, e31, ec3a.symm, e32.symm⟩
    · have qC2 : G.Adj q C2 := (of_decide_eq_true hqC2).symm
      have qA3 : G.Adj q A3 := (of_decide_eq_true hqA3).symm
      have qB3 : G.Adj q B3 := (of_decide_eq_true hqB3).symm
      refine ⟨![B1, A3, B2, C2, C1], ![C3, x, q, A1, A2], B3, fun i => ?_⟩
      fin_cases i
      · exact ⟨e31.symm, ec3a, ec13.symm, ec3b.symm⟩
      · exact ⟨e32, ex2, ex1, ex3.symm⟩
      · exact ⟨ec2b.symm, qC2, qA3, qB3.symm⟩
      · exact ⟨ec12.symm, ec1a.symm, e12, e13.symm⟩
      · exact ⟨ec1b, e21, ec2a.symm, e23.symm⟩
  -- Apply D_3 to the 9 vertices (a1, a2, a3, b1, b2, b3, c1, c2, c3)
  let xs9 : Fin 9 → V := fun i => match i.val with
    | 0 => a1 | 1 => a2 | 2 => a3 | 3 => b1 | 4 => b2 | 5 => b3 | 6 => c1 | 7 => c2 | _ => c3
  obtain ⟨t, ht⟩ := prop_D G hmin 3 (by omega) xs9
  rw [card_filter_fin9] at ht
  have h9 := nine_indep_ge_four
    (decide (G.Adj a1 t)) (decide (G.Adj a2 t)) (decide (G.Adj a3 t))
    (decide (G.Adj b1 t)) (decide (G.Adj b2 t)) (decide (G.Adj b3 t))
    (decide (G.Adj c1 t)) (decide (G.Adj c2 t)) (decide (G.Adj c3 t))
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h12)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h13)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h21)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h23)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h31)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h32)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm hc1a)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm hc2a)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm hc3a)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm hc1b)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm hc2b)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm hc3b)
    ht
  rcases h9 with ⟨ta1, tb1, tc2, tc3⟩ | ⟨ta2, tb2, tc1, tc3⟩ | ⟨ta3, tb3, tc1, tc2⟩
  · exact hbuild a1 a2 a3 b1 b2 b3 t c2 c3
      h12 h13 h21 h23 h31 h32 hx1 hx2 hx3
      (of_decide_eq_true ta1).symm (of_decide_eq_true tb1).symm
      (of_decide_eq_true tc2).symm (of_decide_eq_true tc3).symm
      hc2a.symm hc2b.symm hc3a.symm hc3b.symm
  · exact hbuild a2 a1 a3 b2 b1 b3 t c1 c3
      h21 h23 h12 h13 h32 h31 hx2 hx1 hx3
      (of_decide_eq_true ta2).symm (of_decide_eq_true tb2).symm
      (of_decide_eq_true tc1).symm (of_decide_eq_true tc3).symm
      hc1a.symm hc1b.symm hc3a.symm hc3b.symm
  · exact hbuild a3 a1 a2 b3 b1 b2 t c1 c2
      h31 h32 h13 h12 h23 h21 hx3 hx1 hx2
      (of_decide_eq_true ta3).symm (of_decide_eq_true tb3).symm
      (of_decide_eq_true tc1).symm (of_decide_eq_true tc2).symm
      hc1a.symm hc1b.symm hc2a.symm hc2b.symm

lemma lemma_3_1 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a1 a2 a3 b1 b2 b3 : V)
    (h12 : G.Adj a1 b2) (h13 : G.Adj a1 b3)
    (h21 : G.Adj a2 b1) (h23 : G.Adj a2 b3)
    (h31 : G.Adj a3 b1) (h32 : G.Adj a3 b2)
    (hn1 : ¬ G.Adj a1 b1) (hn2 : ¬ G.Adj a2 b2) (hn3 : ¬ G.Adj a3 b3) :
    ∃ (v u : Fin 5 → V) (w : V),
      ∀ i : Fin 5,
        G.Adj (v i) (v (i + 1)) ∧ G.Adj (u i) (v (i + 1)) ∧
        G.Adj (u i) (v (i + 4)) ∧ G.Adj w (u i) := by
  let xs6 : Fin 6 → V := fun i => match i.val with
    | 0 => a1 | 1 => a2 | 2 => a3 | 3 => b1 | 4 => b2 | _ => b3
  obtain ⟨x, hx⟩ := prop_D G hmin 2 (by omega) xs6
  rw [card_filter_fin6] at hx
  have hcls := c6_indep_ge_three
    (decide (G.Adj a1 x)) (decide (G.Adj a2 x)) (decide (G.Adj a3 x))
    (decide (G.Adj b1 x)) (decide (G.Adj b2 x)) (decide (G.Adj b3 x))
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h12)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h13)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h21)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h23)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h31)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm h32)
    hx
  rcases hcls with ⟨ha1, ha2, ha3⟩ | ⟨hb1, hb2, hb3⟩
  · exact grotzsch_from_c6_step G hcf hmax hmin b1 b2 b3 a1 a2 a3 x
      h21.symm h31.symm h12.symm h32.symm h13.symm h23.symm
      (fun h => hn1 h.symm) (fun h => hn2 h.symm) (fun h => hn3 h.symm)
      (of_decide_eq_true ha1).symm (of_decide_eq_true ha2).symm (of_decide_eq_true ha3).symm
  · exact grotzsch_from_c6_step G hcf hmax hmin a1 a2 a3 b1 b2 b3 x
      h12 h13 h21 h23 h31 h32 hn1 hn2 hn3
      (of_decide_eq_true hb1).symm (of_decide_eq_true hb2).symm (of_decide_eq_true hb3).symm

/- ### Part 3: Andrásfai Graphs Γ_k & Łuczak–Polcyn–Reiher Lemmas 3.2, 3.3, 3.4, Prop. 3.7 -/

lemma and_adj_symm {k i j : ℕ} (hk : 1 ≤ k) (hi : i < 3 * k - 1) (hj : j < 3 * k - 1) :
    (k ≤ (j + (3 * k - 1) - i) % (3 * k - 1) ∧ (j + (3 * k - 1) - i) % (3 * k - 1) ≤ 2 * k - 1) ↔
    (k ≤ (i + (3 * k - 1) - j) % (3 * k - 1) ∧ (i + (3 * k - 1) - j) % (3 * k - 1) ≤ 2 * k - 1) := by
  by_cases hij : i ≤ j
  · have h1 : (j + (3 * k - 1) - i) % (3 * k - 1) = j - i := by
      have : j + (3 * k - 1) - i = (j - i) + (3 * k - 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    by_cases heq : i = j
    · subst heq; exact Iff.rfl
    · have h2 : (i + (3 * k - 1) - j) % (3 * k - 1) = (3 * k - 1) - (j - i) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [h1, h2]; omega
  · have h1 : (i + (3 * k - 1) - j) % (3 * k - 1) = i - j := by
      have : i + (3 * k - 1) - j = (i - j) + (3 * k - 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have h2 : (j + (3 * k - 1) - i) % (3 * k - 1) = (3 * k - 1) - (i - j) := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1, h2]; omega

lemma mod_add_sub {M x y : ℕ} (hy : y < M) : (x % M + M - y) % M = (x + M - y) % M := by
  have h1 : x % M + M * (x / M) = x := Nat.mod_add_div x M
  have h2 : x + M - y = (x % M + M - y) + M * (x / M) := by omega
  rw [h2, Nat.add_mul_mod_self_left]

lemma mod_diff_shift {M x y s : ℕ} (hx : x < M) (hy : y < M) :
    ((y + s) % M + M - (x + s) % M) % M = (y + M - x) % M := by
  have hM : 0 < M := by omega
  have h1 : (y + s) % M + M * ((y + s) / M) = y + s := Nat.mod_add_div (y + s) M
  have h2 : (x + s) % M + M * ((x + s) / M) = x + s := Nat.mod_add_div (x + s) M
  have hxs : (x + s) % M < M := Nat.mod_lt _ hM
  have hys : (y + s) % M < M := Nat.mod_lt _ hM
  by_cases hxy : x ≤ y
  · have hA : (y + M - x) % M = y - x := by
      have : y + M - x = (y - x) + M := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hA]
    have hq : (x + s) / M ≤ (y + s) / M := Nat.div_le_div_right (by omega)
    have hdiff : ((y + s) % M + M - (x + s) % M) + M * ((y + s) / M - (x + s) / M) = (y - x) + M := by
      have hmul : M * ((y + s) / M - (x + s) / M) + M * ((x + s) / M) = M * ((y + s) / M) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hq]
      omega
    have hmod := congrArg (· % M) hdiff
    rw [Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : y - x < M)] at hmod
    exact hmod
  · have hA : (y + M - x) % M = y + M - x := Nat.mod_eq_of_lt (by omega)
    rw [hA]
    have hq : (y + s) / M ≤ (x + s) / M := Nat.div_le_div_right (by omega)
    have hdiff : ((y + s) % M + M - (x + s) % M) = (y + M - x) + M * ((x + s) / M - (y + s) / M) := by
      have hmul : M * ((x + s) / M - (y + s) / M) + M * ((y + s) / M) = M * ((x + s) / M) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hq]
      omega
    rw [hdiff, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

lemma and_common_neighbor {k i j : ℕ} (hk : 1 ≤ k) (hi : i < 3 * k - 1) (hj : j < 3 * k - 1)
    (hnot : ¬ (k ≤ (j + (3 * k - 1) - i) % (3 * k - 1) ∧
               (j + (3 * k - 1) - i) % (3 * k - 1) ≤ 2 * k - 1)) :
    ∃ m : Fin (3 * k - 1),
      (k ≤ (m.val + (3 * k - 1) - i) % (3 * k - 1) ∧ (m.val + (3 * k - 1) - i) % (3 * k - 1) ≤ 2 * k - 1) ∧
      (k ≤ (m.val + (3 * k - 1) - j) % (3 * k - 1) ∧ (m.val + (3 * k - 1) - j) % (3 * k - 1) ≤ 2 * k - 1) := by
  set M := 3 * k - 1
  have hM : 0 < M := by omega
  set d := (j + M - i) % M
  have hd_lt : d < M := Nat.mod_lt _ hM
  have hcase : d < k ∨ 2 * k - 1 < d := by omega
  rcases hcase with hlt | hgt
  · refine ⟨⟨(j + k) % M, Nat.mod_lt _ hM⟩, ?_, ?_⟩
    · rw [mod_add_sub hi]
      have h1 : (j + k + M - i) % M = k + d := by
        have hsum : j + k + M - i = (j + M - i) + k := by omega
        rw [hsum, Nat.add_mod, Nat.mod_eq_of_lt (by omega : k < M), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [h1]; omega
    · rw [mod_add_sub hj]
      have h1 : (j + k + M - j) % M = k := by
        have : j + k + M - j = k + M := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1]; omega
  · have hnot' : ¬ (k ≤ (i + M - j) % M ∧ (i + M - j) % M ≤ 2 * k - 1) :=
      fun h => hnot ((and_adj_symm hk hi hj).mpr h)
    have hd'_lt : (i + M - j) % M < k := by
      have hne : i ≠ j := by
        intro heq; subst heq
        have : d = 0 := by simp only [d, Nat.add_sub_cancel_left, Nat.mod_self]
        omega
      by_cases hij : i ≤ j
      · have h1 : (j + M - i) % M = j - i := by
          have : j + M - i = (j - i) + M := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h2 : (i + M - j) % M = M - (j - i) := by rw [Nat.mod_eq_of_lt (by omega)]; omega
        omega
      · have h1 : (j + M - i) % M = j + M - i := Nat.mod_eq_of_lt (by omega)
        have h2 : (i + M - j) % M = i - j := by
          have : i + M - j = (i - j) + M := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    refine ⟨⟨(i + k) % M, Nat.mod_lt _ hM⟩, ?_, ?_⟩
    · rw [mod_add_sub hi]
      have h1 : (i + k + M - i) % M = k := by
        have : i + k + M - i = k + M := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1]; omega
    · rw [mod_add_sub hj]
      have h1 : (i + k + M - j) % M = k + (i + M - j) % M := by
        have hsum : i + k + M - j = (i + M - j) + k := by omega
        rw [hsum, Nat.add_mod, Nat.mod_eq_of_lt (by omega : k < M), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [h1]; omega

lemma and_hom_injective {V : Type} {G : SimpleGraph V} (hcf : G.CliqueFree 3)
    {k : ℕ} (hk : 1 ≤ k) (g : Fin (3 * k - 1) → V)
    (hg : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j)) :
    Function.Injective g := by
  intro i j hij
  by_contra hne
  have hM : 0 < 3 * k - 1 := by omega
  have hnot_adj : ¬ (k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ∧
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1) := by
    rintro ⟨h1, h2⟩
    have hadj := hg i j h1 h2
    rw [hij] at hadj
    exact G.loopless.irrefl _ hadj
  have hkill : ∀ (a b : Fin (3 * k - 1)), g a = g b →
      1 ≤ (b.val + (3 * k - 1) - a.val) % (3 * k - 1) →
      (b.val + (3 * k - 1) - a.val) % (3 * k - 1) < k → False := by
    intro a b hab hd1 hdk
    set w : Fin (3 * k - 1) := ⟨(b.val + (2 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩
    have hbw : k ≤ (w.val + (3 * k - 1) - b.val) % (3 * k - 1) ∧
        (w.val + (3 * k - 1) - b.val) % (3 * k - 1) ≤ 2 * k - 1 := by
      have : (w.val + (3 * k - 1) - b.val) % (3 * k - 1) = 2 * k - 1 := by
        rw [mod_add_sub b.isLt]
        have : b.val + (2 * k - 1) + (3 * k - 1) - b.val = (2 * k - 1) + (3 * k - 1) := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [this]; omega
    have haw_not : ¬ (k ≤ (w.val + (3 * k - 1) - a.val) % (3 * k - 1) ∧
        (w.val + (3 * k - 1) - a.val) % (3 * k - 1) ≤ 2 * k - 1) := by
      have : (w.val + (3 * k - 1) - a.val) % (3 * k - 1) =
          (b.val + (3 * k - 1) - a.val) % (3 * k - 1) + (2 * k - 1) := by
        rw [mod_add_sub a.isLt]
        have hsum : b.val + (2 * k - 1) + (3 * k - 1) - a.val =
            (b.val + (3 * k - 1) - a.val) + (2 * k - 1) := by omega
        rw [hsum, Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 * k - 1 < 3 * k - 1),
          Nat.mod_eq_of_lt (by omega)]
      rw [this]; omega
    obtain ⟨u, hau, huw⟩ := and_common_neighbor hk a.isLt w.isLt haw_not
    have e1 : G.Adj (g a) (g u) := hg a u hau.1 hau.2
    have e2 : G.Adj (g w) (g u) := hg w u huw.1 huw.2
    have e3 : G.Adj (g b) (g w) := hg b w hbw.1 hbw.2
    rw [← hab] at e3
    exact not_adj_both hcf e1 e3 e2.symm
  have hne_val : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_cases hlt : (j.val + (3 * k - 1) - i.val) % (3 * k - 1) < k
  · have hpos : 1 ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) := by
      by_cases h : i.val ≤ j.val
      · have : (j.val + (3 * k - 1) - i.val) % (3 * k - 1) = j.val - i.val := by
          have : j.val + (3 * k - 1) - i.val = (j.val - i.val) + (3 * k - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have : (j.val + (3 * k - 1) - i.val) % (3 * k - 1) = j.val + (3 * k - 1) - i.val :=
          Nat.mod_eq_of_lt (by omega)
        omega
    exact hkill i j hij hpos hlt
  · have hlt' : (i.val + (3 * k - 1) - j.val) % (3 * k - 1) < k := by
      have hgt : 2 * k - 1 < (j.val + (3 * k - 1) - i.val) % (3 * k - 1) := by omega
      by_cases h : i.val ≤ j.val
      · have h1 : (j.val + (3 * k - 1) - i.val) % (3 * k - 1) = j.val - i.val := by
          have : j.val + (3 * k - 1) - i.val = (j.val - i.val) + (3 * k - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h2 : (i.val + (3 * k - 1) - j.val) % (3 * k - 1) = (3 * k - 1) - (j.val - i.val) := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        omega
      · have h1 : (j.val + (3 * k - 1) - i.val) % (3 * k - 1) = j.val + (3 * k - 1) - i.val :=
          Nat.mod_eq_of_lt (by omega)
        have h2 : (i.val + (3 * k - 1) - j.val) % (3 * k - 1) = i.val - j.val := by
          have : i.val + (3 * k - 1) - j.val = (i.val - j.val) + (3 * k - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    have hpos' : 1 ≤ (i.val + (3 * k - 1) - j.val) % (3 * k - 1) := by
      by_cases h : j.val ≤ i.val
      · have : (i.val + (3 * k - 1) - j.val) % (3 * k - 1) = i.val - j.val := by
          have : i.val + (3 * k - 1) - j.val = (i.val - j.val) + (3 * k - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have : (i.val + (3 * k - 1) - j.val) % (3 * k - 1) = i.val + (3 * k - 1) - j.val :=
          Nat.mod_eq_of_lt (by omega)
        omega
    exact hkill j i hij.symm hpos' hlt'

lemma and_twin_nonadj_of_nonadj {V : Type} {G : SimpleGraph V} (hcf : G.CliqueFree 3)
    {k : ℕ} (hk : 1 ≤ k) (g : Fin (3 * k - 1) → V)
    (hg : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j))
    {x y : V} {a b : Fin (3 * k - 1)}
    (hx : ∀ t : Fin (3 * k - 1), G.Adj x (g t) ↔ G.Adj (g a) (g t))
    (hy : ∀ t : Fin (3 * k - 1), G.Adj y (g t) ↔ G.Adj (g b) (g t))
    (hnot : ¬ (k ≤ (b.val + (3 * k - 1) - a.val) % (3 * k - 1) ∧
               (b.val + (3 * k - 1) - a.val) % (3 * k - 1) ≤ 2 * k - 1)) :
    ¬ G.Adj x y := by
  obtain ⟨m, ham, hbm⟩ := and_common_neighbor hk a.isLt b.isLt hnot
  have hxm : G.Adj x (g m) := (hx m).mpr (hg a m ham.1 ham.2)
  have hym : G.Adj y (g m) := (hy m).mpr (hg b m hbm.1 hbm.2)
  exact fun hxy => not_adj_both hcf hxm.symm hym.symm hxy

-- Lemma 3.2 base case (k = 3, edge 0-4)
lemma lemma_3_2_base {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hnoC6 : ∀ a1 a2 a3 b1 b2 b3 : V,
      G.Adj a1 b2 → G.Adj a1 b3 → G.Adj a2 b1 → G.Adj a2 b3 → G.Adj a3 b1 → G.Adj a3 b2 →
      ¬ G.Adj a1 b1 → ¬ G.Adj a2 b2 → G.Adj a3 b3)
    (g : Fin 8 → V)
    (hg : ∀ i j : Fin 8,
      3 ≤ (j.val + 8 - i.val) % 8 → (j.val + 8 - i.val) % 8 ≤ 5 → G.Adj (g i) (g j))
    {p q : V}
    (hp : ∀ t : Fin 8, G.Adj p (g t) ↔ G.Adj (g 0) (g t))
    (hq : ∀ t : Fin 8, G.Adj q (g t) ↔ G.Adj (g 4) (g t)) :
    G.Adj p q := by
  by_contra hnpq
  have hne : p ≠ q := by
    intro h; subst h
    have h1 : G.Adj p (g 3) := (hp 3).mpr (hg 0 3 (by decide) (by decide))
    have h2 : G.Adj p (g 7) := (hq 7).mpr (hg 4 7 (by decide) (by decide))
    exact not_adj_both hcf h1 h2 (hg 3 7 (by decide) (by decide))
  obtain ⟨r, hrp, hrq⟩ := hmax p q hne hnpq
  have hp5 : G.Adj p (g 5) := (hp 5).mpr (hg 0 5 (by decide) (by decide))
  have hq7 : G.Adj q (g 7) := (hq 7).mpr (hg 4 7 (by decide) (by decide))
  have hp7 : ¬ G.Adj p (g 7) := fun h =>
    not_adj_both hcf ((hp 7).mp h) (hg 0 4 (by decide) (by decide)) (hg 7 4 (by decide) (by decide))
  have hq5 : ¬ G.Adj q (g 5) := fun h =>
    not_adj_both hcf ((hq 5).mp h) (hg 4 0 (by decide) (by decide)) (hg 5 0 (by decide) (by decide))
  have hr2 : G.Adj r (g 2) :=
    (hnoC6 p q (g 2) (g 7) (g 5) r
      hp5 hrp hq7 hrq (hg 2 7 (by decide) (by decide)) (hg 2 5 (by decide) (by decide))
      hp7 hq5).symm
  have hp3 : G.Adj p (g 3) := (hp 3).mpr (hg 0 3 (by decide) (by decide))
  have hq1 : G.Adj q (g 1) := (hq 1).mpr (hg 4 1 (by decide) (by decide))
  have hp1 : ¬ G.Adj p (g 1) := fun h =>
    not_adj_both hcf ((hp 1).mp h) (hg 0 4 (by decide) (by decide)) (hg 1 4 (by decide) (by decide))
  have hq3 : ¬ G.Adj q (g 3) := fun h =>
    not_adj_both hcf ((hq 3).mp h) (hg 4 0 (by decide) (by decide)) (hg 3 0 (by decide) (by decide))
  have hr6 : G.Adj r (g 6) :=
    (hnoC6 p q (g 6) (g 1) (g 3) r
      hp3 hrp hq1 hrq (hg 6 1 (by decide) (by decide)) (hg 6 3 (by decide) (by decide))
      hp1 hq3).symm
  exact not_adj_both hcf hr2 hr6 (hg 2 6 (by decide) (by decide))

-- Lemma 3.2: every long edge (k < j < 2k - 1) of Γ_k has the twin property
lemma lemma_3_2 {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hnoC6 : ∀ a1 a2 a3 b1 b2 b3 : V,
      G.Adj a1 b2 → G.Adj a1 b3 → G.Adj a2 b1 → G.Adj a2 b3 → G.Adj a3 b1 → G.Adj a3 b2 →
      ¬ G.Adj a1 b1 → ¬ G.Adj a2 b2 → G.Adj a3 b3)
    {k : ℕ} (hk : 3 ≤ k) (g : Fin (3 * k - 1) → V)
    (hg : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j))
    {j : Fin (3 * k - 1)} (hj1 : k < j.val) (hj2 : j.val < 2 * k - 1)
    {p q : V}
    (hp : ∀ t : Fin (3 * k - 1), G.Adj p (g t) ↔ G.Adj (g ⟨0, by omega⟩) (g t))
    (hq : ∀ t : Fin (3 * k - 1), G.Adj q (g t) ↔ G.Adj (g j) (g t)) :
    G.Adj p q := by
  let emb : Fin 8 → Fin (3 * k - 1) := fun a =>
    match a.val with
    | 0 => ⟨0, by omega⟩
    | 1 => ⟨j.val - k, by omega⟩
    | 2 => ⟨k - 1, by omega⟩
    | 3 => ⟨k, by omega⟩
    | 4 => j
    | 5 => ⟨2 * k - 1, by omega⟩
    | 6 => ⟨2 * k, by omega⟩
    | _ => ⟨j.val + k, by omega⟩
  have hdiff_eq : ∀ x y : ℕ, x < 3 * k - 1 → y < 3 * k - 1 →
      (y + (3 * k - 1) - x) % (3 * k - 1) =
      if x ≤ y then y - x else y + (3 * k - 1) - x := by
    intro x y hx hy
    split_ifs with h
    · have : y + (3 * k - 1) - x = (y - x) + (3 * k - 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  have hemb_adj : ∀ a b : Fin 8,
      3 ≤ (b.val + 8 - a.val) % 8 → (b.val + 8 - a.val) % 8 ≤ 5 →
      G.Adj (g (emb a)) (g (emb b)) := by
    intro a b h1 h2
    apply hg (emb a) (emb b)
    · rw [hdiff_eq _ _ (emb a).isLt (emb b).isLt]
      fin_cases a <;> fin_cases b <;>
        (simp only [emb] at *; split_ifs <;> omega)
    · rw [hdiff_eq _ _ (emb a).isLt (emb b).isLt]
      fin_cases a <;> fin_cases b <;>
        (simp only [emb] at *; split_ifs <;> omega)
  exact lemma_3_2_base hcf hmax hnoC6 (fun a => g (emb a)) hemb_adj
    (fun t => hp (emb t)) (fun t => hq (emb t))

lemma gamma_next_idx_adj (k a b ia ib : ℕ) (hk : 1 ≤ k)
    (ha : a < 3 * k + 2) (hb : b < 3 * k + 2)
    (hia : ia < 3 * k - 1) (_hib : ib < 3 * k - 1)
    (hA : (a = 0 ∧ ia = 0) ∨ (1 ≤ a ∧ a < k ∧ ia = a) ∨ (a = k ∧ ia = k) ∨
          (k + 1 ≤ a ∧ a ≤ 2 * k ∧ ia = a - 1) ∨ (2 * k + 2 ≤ a ∧ a ≤ 3 * k ∧ ia = a - 2) ∨
          (a = 3 * k + 1 ∧ ia = 0))
    (hB : (b = 0 ∧ ib = 0) ∨ (1 ≤ b ∧ b < k ∧ ib = b) ∨ (b = k ∧ ib = k) ∨
          (k + 1 ≤ b ∧ b ≤ 2 * k ∧ ib = b - 1) ∨ (2 * k + 2 ≤ b ∧ b ≤ 3 * k ∧ ib = b - 2) ∨
          (b = 3 * k + 1 ∧ ib = 0))
    (h1 : k + 1 ≤ (if a ≤ b then b - a else b + (3 * k + 2) - a))
    (h2 : (if a ≤ b then b - a else b + (3 * k + 2) - a) ≤ 2 * k + 1) :
    k ≤ (if ia ≤ ib then ib - ia else ib + (3 * k - 1) - ia) ∧
    (if ia ≤ ib then ib - ia else ib + (3 * k - 1) - ia) ≤ 2 * k - 1 := by
  by_cases hab : a ≤ b <;> by_cases hiab : ia ≤ ib
  all_goals simp only [hab, hiab, ite_true, ite_false] at h1 h2 ⊢
  all_goals rcases hA with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩
  all_goals rcases hB with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩
  all_goals omega

-- Lemma 3.3: short edge 0 - k has the twin property when G is Γ_{k+1}-free
lemma lemma_3_3_short {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hnoC6 : ∀ a1 a2 a3 b1 b2 b3 : V,
      G.Adj a1 b2 → G.Adj a1 b3 → G.Adj a2 b1 → G.Adj a2 b3 → G.Adj a3 b1 → G.Adj a3 b2 →
      ¬ G.Adj a1 b1 → ¬ G.Adj a2 b2 → G.Adj a3 b3)
    {k : ℕ} (hk : 1 ≤ k)
    (hnoNext : ¬ ∃ g' : Fin (3 * (k + 1) - 1) → V, ∀ i j : Fin (3 * (k + 1) - 1),
      k + 1 ≤ (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) →
      (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) ≤ 2 * (k + 1) - 1 →
      G.Adj (g' i) (g' j))
    (g : Fin (3 * k - 1) → V)
    (hg : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j))
    {p q : V}
    (hp : ∀ t : Fin (3 * k - 1), G.Adj p (g t) ↔ G.Adj (g ⟨0, by omega⟩) (g t))
    (hq : ∀ t : Fin (3 * k - 1), G.Adj q (g t) ↔ G.Adj (g ⟨k, by omega⟩) (g t)) :
    G.Adj p q := by
  by_contra hnpq
  have hne : p ≠ q := by
    intro h; subst h
    have h1 : G.Adj p (g ⟨k, by omega⟩) :=
      (hp ⟨k, by omega⟩).mpr (hg ⟨0, by omega⟩ ⟨k, by omega⟩
        (by dsimp only; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])
        (by dsimp only; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega))
    have h2 : G.Adj (g ⟨k, by omega⟩) (g ⟨k, by omega⟩) := (hq ⟨k, by omega⟩).mp h1
    exact G.loopless.irrefl _ h2
  obtain ⟨r, hrp, hrq⟩ := hmax p q hne hnpq
  -- Show r is adjacent to g(j) for every 0 < j < k
  have hrj : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j < k), G.Adj r (g ⟨j, by omega⟩) := by
    intro j hj1 hj2
    let u1 : Fin (3 * k - 1) := ⟨j + k, by omega⟩
    let u2 : Fin (3 * k - 1) := ⟨j + 2 * k - 1, by omega⟩
    let vj : Fin (3 * k - 1) := ⟨j, by omega⟩
    have hpu1 : G.Adj p (g u1) := (hp u1).mpr (hg ⟨0, by omega⟩ u1
      (by dsimp only [u1]; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
      (by dsimp only [u1]; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega))
    have hqu2 : G.Adj q (g u2) := (hq u2).mpr (hg ⟨k, by omega⟩ u2
      (by dsimp only [u2]
          have h' : j + 2 * k - 1 + (3 * k - 1) - k = (j + k - 1) + (3 * k - 1) := by omega
          rw [h', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
      (by dsimp only [u2]
          have h' : j + 2 * k - 1 + (3 * k - 1) - k = (j + k - 1) + (3 * k - 1) := by omega
          rw [h', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega))
    have hvju1 : G.Adj (g vj) (g u1) := hg vj u1
      (by dsimp only [vj, u1]
          have h' : j + k + (3 * k - 1) - j = k + (3 * k - 1) := by omega
          rw [h', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])
      (by dsimp only [vj, u1]
          have h' : j + k + (3 * k - 1) - j = k + (3 * k - 1) := by omega
          rw [h', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
    have hvju2 : G.Adj (g vj) (g u2) := hg vj u2
      (by dsimp only [vj, u2]
          have h' : j + 2 * k - 1 + (3 * k - 1) - j = (2 * k - 1) + (3 * k - 1) := by omega
          rw [h', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
      (by dsimp only [vj, u2]
          have h' : j + 2 * k - 1 + (3 * k - 1) - j = (2 * k - 1) + (3 * k - 1) := by omega
          rw [h', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])
    have hnpu2 : ¬ G.Adj p (g u2) := by
      apply and_twin_nonadj_of_nonadj hcf hk g hg hp (fun _ => Iff.rfl)
      dsimp only [u2]; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    have hnqu1 : ¬ G.Adj q (g u1) := by
      apply and_twin_nonadj_of_nonadj hcf hk g hg hq (fun _ => Iff.rfl)
      dsimp only [u1]
      have h' : j + k + (3 * k - 1) - k = j + (3 * k - 1) := by omega
      rw [h', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    exact (hnoC6 p q (g vj) (g u2) (g u1) r
      hpu1 hrp hqu2 hrq hvju2 hvju1 hnpu2 hnqu1).symm
  -- Build a homomorphism from Γ_{k+1} into G to contradict hnoNext!
  apply hnoNext
  let g' : Fin (3 * (k + 1) - 1) → V := fun a =>
    if ha0 : a.val = 0 then p
    else if ha1 : a.val < k then g ⟨a.val, by omega⟩
    else if ha2 : a.val = k then q
    else if ha3 : a.val ≤ 2 * k then g ⟨a.val - 1, by omega⟩
    else if ha4 : a.val = 2 * k + 1 then r
    else if ha5 : a.val ≤ 3 * k then g ⟨a.val - 2, by omega⟩
    else g ⟨0, by omega⟩
  refine ⟨g', fun a b h1 h2 => ?_⟩
  have h1' : k + 1 ≤ (b.val + (3 * k + 2) - a.val) % (3 * k + 2) := by
    have hM1 : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
    have h1'' := h1; revert h1''; generalize a.val = av; generalize b.val = bv; rw [hM1]; exact id
  have h2' : (b.val + (3 * k + 2) - a.val) % (3 * k + 2) ≤ 2 * k + 1 := by
    have hM1 : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
    have hM2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have h2'' := h2; revert h2''; generalize a.val = av; generalize b.val = bv; rw [hM1, hM2]; exact id
  have ha_lt : a.val < 3 * k + 2 := by omega
  have hb_lt : b.val < 3 * k + 2 := by omega
  -- Helper: map any vertex ≠ r to its Γ_k-index
  have hnotr : ∀ c : Fin (3 * (k + 1) - 1), c.val ≠ 2 * k + 1 →
      ∃ idx : Fin (3 * k - 1),
        (∀ t : Fin (3 * k - 1), G.Adj (g' c) (g t) ↔ G.Adj (g idx) (g t)) ∧
        ((c.val = 0 ∧ idx.val = 0) ∨ (1 ≤ c.val ∧ c.val < k ∧ idx.val = c.val) ∨
         (c.val = k ∧ idx.val = k) ∨ (k + 1 ≤ c.val ∧ c.val ≤ 2 * k ∧ idx.val = c.val - 1) ∨
         (2 * k + 2 ≤ c.val ∧ c.val ≤ 3 * k ∧ idx.val = c.val - 2) ∨
         (c.val = 3 * k + 1 ∧ idx.val = 0)) ∧
        (c.val ≠ 0 → c.val ≠ k → g' c = g idx) := by
    intro c hcr
    by_cases c0 : c.val = 0
    · refine ⟨⟨0, by omega⟩, ?_, Or.inl ⟨c0, rfl⟩, by omega⟩
      intro t; simp only [g', dif_pos c0]; exact hp t
    · by_cases c1 : c.val < k
      · refine ⟨⟨c.val, by omega⟩, ?_, Or.inr (Or.inl ⟨by omega, c1, rfl⟩), ?_⟩
        · intro t; simp only [g', dif_neg c0, dif_pos c1]
        · intro _ _; simp only [g', dif_neg c0, dif_pos c1]
      · by_cases c2 : c.val = k
        · refine ⟨⟨k, by omega⟩, ?_, Or.inr (Or.inr (Or.inl ⟨c2, rfl⟩)), by omega⟩
          intro t; simp only [g', dif_neg c0, dif_neg c1, dif_pos c2]; exact hq t
        · by_cases c3 : c.val ≤ 2 * k
          · refine ⟨⟨c.val - 1, by omega⟩, ?_, Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, c3, rfl⟩))), ?_⟩
            · intro t; simp only [g', dif_neg c0, dif_neg c1, dif_neg c2, dif_pos c3]
            · intro _ _; simp only [g', dif_neg c0, dif_neg c1, dif_neg c2, dif_pos c3]
          · by_cases c5 : c.val ≤ 3 * k
            · refine ⟨⟨c.val - 2, by omega⟩, ?_,
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, c5, rfl⟩)))), ?_⟩
              · intro t; simp only [g', dif_neg c0, dif_neg c1, dif_neg c2, dif_neg c3, dif_neg hcr, dif_pos c5]
              · intro _ _; simp only [g', dif_neg c0, dif_neg c1, dif_neg c2, dif_neg c3, dif_neg hcr, dif_pos c5]
            · refine ⟨⟨0, by omega⟩, ?_,
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))), ?_⟩
              · intro t; simp only [g', dif_neg c0, dif_neg c1, dif_neg c2, dif_neg c3, dif_neg hcr, dif_neg c5]
              · intro _ _; simp only [g', dif_neg c0, dif_neg c1, dif_neg c2, dif_neg c3, dif_neg hcr, dif_neg c5]
  -- Case 1: a is r (a.val = 2*k + 1)
  by_cases har : a.val = 2 * k + 1
  · have hga : g' a = r := by
      simp only [g', dif_neg (show a.val ≠ 0 by omega), dif_neg (show ¬ a.val < k by omega),
        dif_neg (show a.val ≠ k by omega), dif_neg (show ¬ a.val ≤ 2 * k by omega), dif_pos har]
    rw [hga]
    have hb_le : b.val ≤ k := by
      by_cases hba : a.val ≤ b.val
      · have : (b.val + (3 * k + 2) - a.val) % (3 * k + 2) = b.val - a.val := by
          have : b.val + (3 * k + 2) - a.val = (b.val - a.val) + (3 * k + 2) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have : (b.val + (3 * k + 2) - a.val) % (3 * k + 2) = b.val + (3 * k + 2) - a.val :=
          Nat.mod_eq_of_lt (by omega)
        omega
    by_cases b0 : b.val = 0
    · simp only [g', dif_pos b0]; exact hrp.symm
    · by_cases bk : b.val = k
      · simp only [g', dif_neg (show b.val ≠ 0 by omega), dif_neg (show ¬ b.val < k by omega), dif_pos bk]
        exact hrq.symm
      · have b1 : b.val < k := by omega
        simp only [g', dif_neg b0, dif_pos b1]
        exact hrj b.val (by omega) b1
  -- Case 2: b is r (b.val = 2*k + 1)
  · by_cases hbr : b.val = 2 * k + 1
    · have hgb : g' b = r := by
        simp only [g', dif_neg (show b.val ≠ 0 by omega), dif_neg (show ¬ b.val < k by omega),
          dif_neg (show b.val ≠ k by omega), dif_neg (show ¬ b.val ≤ 2 * k by omega), dif_pos hbr]
      rw [hgb]
      have ha_le : a.val ≤ k := by
        by_cases hab : a.val ≤ b.val
        · have : (b.val + (3 * k + 2) - a.val) % (3 * k + 2) = b.val - a.val := by
            have : b.val + (3 * k + 2) - a.val = (b.val - a.val) + (3 * k + 2) := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          omega
        · have : (b.val + (3 * k + 2) - a.val) % (3 * k + 2) = b.val + (3 * k + 2) - a.val :=
            Nat.mod_eq_of_lt (by omega)
          omega
      by_cases a0 : a.val = 0
      · simp only [g', dif_pos a0]; exact hrp
      · by_cases ak : a.val = k
        · simp only [g', dif_neg (show a.val ≠ 0 by omega), dif_neg (show ¬ a.val < k by omega), dif_pos ak]
          exact hrq
        · have a1 : a.val < k := by omega
          simp only [g', dif_neg a0, dif_pos a1]
          exact (hrj a.val (by omega) a1).symm
    -- Case 3: neither a nor b is r!
    · obtain ⟨ia, hia_tw, hsegA, ha_eq⟩ := hnotr a har
      obtain ⟨ib, hib_tw, hsegB, hb_eq⟩ := hnotr b hbr
      have hdiff_ab : (b.val + (3 * k + 2) - a.val) % (3 * k + 2) =
          if a.val ≤ b.val then b.val - a.val else b.val + (3 * k + 2) - a.val := by
        split_ifs with h
        · have : b.val + (3 * k + 2) - a.val = (b.val - a.val) + (3 * k + 2) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · exact Nat.mod_eq_of_lt (by omega)
      have hdiff_i : (ib.val + (3 * k - 1) - ia.val) % (3 * k - 1) =
          if ia.val ≤ ib.val then ib.val - ia.val else ib.val + (3 * k - 1) - ia.val := by
        split_ifs with h
        · have : ib.val + (3 * k - 1) - ia.val = (ib.val - ia.val) + (3 * k - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · exact Nat.mod_eq_of_lt (by omega)
      rw [hdiff_ab] at h1' h2'
      have hadj_idx : k ≤ (ib.val + (3 * k - 1) - ia.val) % (3 * k - 1) ∧
          (ib.val + (3 * k - 1) - ia.val) % (3 * k - 1) ≤ 2 * k - 1 := by
        rw [hdiff_i]
        exact gamma_next_idx_adj k a.val b.val ia.val ib.val hk ha_lt hb_lt ia.isLt ib.isLt hsegA hsegB h1' h2'
      have hg_edge : G.Adj (g ia) (g ib) := hg ia ib hadj_idx.1 hadj_idx.2
      by_cases ha0k : a.val = 0 ∨ a.val = k
      · by_cases hb0k : b.val = 0 ∨ b.val = k
        · exfalso
          rcases ha0k with ea | ea <;> rcases hb0k with eb | eb <;>
            (rw [ea, eb] at h1' h2'; split_ifs at h1' h2' <;> omega)
        · have hb_g : g' b = g ib := hb_eq (fun e => hb0k (Or.inl e)) (fun e => hb0k (Or.inr e))
          rw [hb_g]; exact (hia_tw ib).mpr hg_edge
      · have ha_g : g' a = g ia := ha_eq (fun e => ha0k (Or.inl e)) (fun e => ha0k (Or.inr e))
        rw [ha_g]; exact ((hib_tw ia).mpr hg_edge.symm).symm

-- Full Twin Lemma (Lemma 3.3): ALL edges of Γ_k have the twin property when G is Γ_{k+1}-free!
lemma lemma_3_3 {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hnoC6 : ∀ a1 a2 a3 b1 b2 b3 : V,
      G.Adj a1 b2 → G.Adj a1 b3 → G.Adj a2 b1 → G.Adj a2 b3 → G.Adj a3 b1 → G.Adj a3 b2 →
      ¬ G.Adj a1 b1 → ¬ G.Adj a2 b2 → G.Adj a3 b3)
    {k : ℕ} (hk : 1 ≤ k)
    (hnoNext : ¬ ∃ g' : Fin (3 * (k + 1) - 1) → V, ∀ i j : Fin (3 * (k + 1) - 1),
      k + 1 ≤ (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) →
      (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) ≤ 2 * (k + 1) - 1 →
      G.Adj (g' i) (g' j))
    (g : Fin (3 * k - 1) → V)
    (hg : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j))
    {a b : Fin (3 * k - 1)}
    (hab1 : k ≤ (b.val + (3 * k - 1) - a.val) % (3 * k - 1))
    (hab2 : (b.val + (3 * k - 1) - a.val) % (3 * k - 1) ≤ 2 * k - 1)
    {p q : V}
    (hp : ∀ t : Fin (3 * k - 1), G.Adj p (g t) ↔ G.Adj (g a) (g t))
    (hq : ∀ t : Fin (3 * k - 1), G.Adj q (g t) ↔ G.Adj (g b) (g t)) :
    G.Adj p q := by
  have hM : 0 < 3 * k - 1 := by omega
  -- Rotate g by a so that a becomes 0 and b becomes d = (b - a) % (3 * k - 1)!
  let rot : Fin (3 * k - 1) → Fin (3 * k - 1) := fun t => ⟨(t.val + a.val) % (3 * k - 1), Nat.mod_lt _ hM⟩
  have hrot_adj : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 →
      G.Adj (g (rot i)) (g (rot j)) := fun i j h1 h2 => by
    apply hg (rot i) (rot j)
    · dsimp only [rot]; rw [mod_diff_shift i.isLt j.isLt]; exact h1
    · dsimp only [rot]; rw [mod_diff_shift i.isLt j.isLt]; exact h2
  have hrot0 : rot ⟨0, hM⟩ = a := Fin.ext (by simp only [rot, zero_add]; exact Nat.mod_eq_of_lt a.isLt)
  let d : Fin (3 * k - 1) := ⟨(b.val + (3 * k - 1) - a.val) % (3 * k - 1), Nat.mod_lt _ hM⟩
  have hrotd : rot d = b := by
    apply Fin.ext
    dsimp only [rot, d]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : b.val + (3 * k - 1) - a.val + a.val = b.val + (3 * k - 1) := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]
  have hp' : ∀ t : Fin (3 * k - 1), G.Adj p (g (rot t)) ↔ G.Adj (g (rot ⟨0, hM⟩)) (g (rot t)) := fun t => by
    rw [hrot0]; exact hp (rot t)
  have hq' : ∀ t : Fin (3 * k - 1), G.Adj q (g (rot t)) ↔ G.Adj (g (rot d)) (g (rot t)) := fun t => by
    rw [hrotd]; exact hq (rot t)
  by_cases hd1 : d.val = k
  · have hdeq : d = ⟨k, by omega⟩ := Fin.ext hd1
    rw [hdeq] at hq'
    exact lemma_3_3_short hcf hmax hnoC6 hk hnoNext (fun t => g (rot t)) hrot_adj hp' hq'
  · by_cases hd2 : d.val = 2 * k - 1
    · -- Swap p and q! Since (0 - (2k-1)) % (3k-1) = k, this is a short edge in reverse!
      let rot2 : Fin (3 * k - 1) → Fin (3 * k - 1) := fun t => ⟨(t.val + b.val) % (3 * k - 1), Nat.mod_lt _ hM⟩
      have hrot2_adj : ∀ i j : Fin (3 * k - 1),
          k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
          (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 →
          G.Adj (g (rot2 i)) (g (rot2 j)) := fun i j h1 h2 => by
        apply hg (rot2 i) (rot2 j)
        · dsimp only [rot2]; rw [mod_diff_shift i.isLt j.isLt]; exact h1
        · dsimp only [rot2]; rw [mod_diff_shift i.isLt j.isLt]; exact h2
      have hrot2_0 : rot2 ⟨0, hM⟩ = b := Fin.ext (by simp only [rot2, zero_add]; exact Nat.mod_eq_of_lt b.isLt)
      have hrot2_k : rot2 ⟨k, by omega⟩ = a := by
        apply Fin.ext
        dsimp only [rot2]
        have hba : (a.val + (3 * k - 1) - b.val) % (3 * k - 1) = k := by
          dsimp only [d] at hd2
          by_cases h : a.val ≤ b.val
          · have h1 : (b.val + (3 * k - 1) - a.val) % (3 * k - 1) = b.val - a.val := by
              have : b.val + (3 * k - 1) - a.val = (b.val - a.val) + (3 * k - 1) := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have h2 : (a.val + (3 * k - 1) - b.val) % (3 * k - 1) = (3 * k - 1) - (b.val - a.val) := by
              rw [Nat.mod_eq_of_lt (by omega)]; omega
            omega
          · have h1 : (b.val + (3 * k - 1) - a.val) % (3 * k - 1) = b.val + (3 * k - 1) - a.val :=
              Nat.mod_eq_of_lt (by omega)
            have h2 : (a.val + (3 * k - 1) - b.val) % (3 * k - 1) = a.val - b.val := by
              have : a.val + (3 * k - 1) - b.val = (a.val - b.val) + (3 * k - 1) := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
        calc (k + b.val) % (3 * k - 1)
            = ((a.val + (3 * k - 1) - b.val) % (3 * k - 1) + b.val) % (3 * k - 1) := by rw [hba]
          _ = (a.val + (3 * k - 1) - b.val + b.val) % (3 * k - 1) := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          _ = (a.val + (3 * k - 1)) % (3 * k - 1) := by congr 1; omega
          _ = a.val := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]
      exact (lemma_3_3_short hcf hmax hnoC6 hk hnoNext (fun t => g (rot2 t)) hrot2_adj
        (fun t => by rw [hrot2_0]; exact hq (rot2 t))
        (fun t => by rw [hrot2_k]; exact hp (rot2 t))).symm
    · have hk3 : 3 ≤ k := by dsimp only [d] at hd1 hd2; omega
      exact lemma_3_2 hcf hmax hnoC6 hk3 (fun t => g (rot t)) hrot_adj
        (by dsimp only [d] at hd1 ⊢; omega) (by dsimp only [d] at hd2 ⊢; omega) hp' hq'

-- Lemma 2.3 (Twin replacement lemma for Γ_k)
lemma lemma_2_3_and {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hnoC6 : ∀ a1 a2 a3 b1 b2 b3 : V,
      G.Adj a1 b2 → G.Adj a1 b3 → G.Adj a2 b1 → G.Adj a2 b3 → G.Adj a3 b1 → G.Adj a3 b2 →
      ¬ G.Adj a1 b1 → ¬ G.Adj a2 b2 → G.Adj a3 b3)
    {k : ℕ} (hk : 1 ≤ k)
    (hnoNext : ¬ ∃ g' : Fin (3 * (k + 1) - 1) → V, ∀ i j : Fin (3 * (k + 1) - 1),
      k + 1 ≤ (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) →
      (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) ≤ 2 * (k + 1) - 1 →
      G.Adj (g' i) (g' j))
    (g : Fin (3 * k - 1) → V)
    (hg : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j))
    {z_idx q_idx : Fin (3 * k - 1)} (hqz_ne : q_idx ≠ z_idx)
    {z' q' : V}
    (hz' : ∀ t : Fin (3 * k - 1), G.Adj z' (g t) ↔ G.Adj (g z_idx) (g t))
    (hq' : ∀ t : Fin (3 * k - 1),
      G.Adj q' (if t = z_idx then z' else g t) ↔
      G.Adj (g q_idx) (if t = z_idx then z' else g t)) :
    ∀ t : Fin (3 * k - 1), G.Adj q' (g t) ↔ G.Adj (g q_idx) (g t) := by
  intro t
  by_cases ht : t = z_idx
  · subst ht
    by_cases hadj : k ≤ (t.val + (3 * k - 1) - q_idx.val) % (3 * k - 1) ∧
        (t.val + (3 * k - 1) - q_idx.val) % (3 * k - 1) ≤ 2 * k - 1
    · have hgt : G.Adj (g q_idx) (g t) := hg q_idx t hadj.1 hadj.2
      -- g' = replacing g t by z' is still a valid Γ_k!
      let g' : Fin (3 * k - 1) → V := fun s => if s = t then z' else g s
      have hg' : ∀ i j : Fin (3 * k - 1),
          k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
          (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 →
          G.Adj (g' i) (g' j) := by
        intro i j h1 h2
        by_cases hi : i = t
        · have hj : j ≠ t := fun h => by
            rw [hi, h] at h1
            have : t.val + (3 * k - 1) - t.val = 3 * k - 1 := by omega
            rw [this, Nat.mod_self] at h1; omega
          simp only [g', if_pos hi, if_neg hj]
          rw [hi] at h1 h2; exact (hz' j).mpr (hg t j h1 h2)
        · by_cases hj : j = t
          · subst hj
            simp only [g', if_neg hi, if_pos rfl]
            exact ((hz' i).mpr (hg j i ((and_adj_symm hk i.isLt j.isLt).mp ⟨h1, h2⟩).1
              ((and_adj_symm hk i.isLt j.isLt).mp ⟨h1, h2⟩).2)).symm
          · simp only [g', if_neg hi, if_neg hj]; exact hg i j h1 h2
      have hq'_tw : ∀ s : Fin (3 * k - 1), G.Adj q' (g' s) ↔ G.Adj (g' q_idx) (g' s) := by
        intro s; simp only [g', if_neg hqz_ne]; exact hq' s
      have hgt_tw : ∀ s : Fin (3 * k - 1), G.Adj (g t) (g' s) ↔ G.Adj (g' t) (g' s) := by
        intro s
        by_cases hs : s = t
        · subst hs; simp only [g', if_pos rfl]
          have h1 : ¬ G.Adj (g s) z' := fun h => G.loopless.irrefl _ ((hz' s).mp h.symm)
          have h2 : ¬ G.Adj z' z' := G.loopless.irrefl z'
          exact ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
        · simp only [g', if_neg hs, if_pos rfl]; exact (hz' s).symm
      have hq't : G.Adj q' (g t) := lemma_3_3 hcf hmax hnoC6 hk hnoNext g' hg' hadj.1 hadj.2 hq'_tw hgt_tw
      exact ⟨fun _ => hgt, fun _ => hq't⟩
    · obtain ⟨y, hqy, hty⟩ := and_common_neighbor hk q_idx.isLt t.isLt hadj
      have hyt : y ≠ t := fun h => by
        subst h
        have h1 := hty.1
        have : y.val + (3 * k - 1) - y.val = 3 * k - 1 := by omega
        rw [this, Nat.mod_self] at h1; omega
      have hq'y : G.Adj q' (g y) := by
        have := (hq' y).mpr (by simp only [if_neg hyt]; exact hg q_idx y hqy.1 hqy.2)
        simpa only [if_neg hyt] using this
      have hty_g : G.Adj (g t) (g y) := hg t y hty.1 hty.2
      have hn1 : ¬ G.Adj q' (g t) := fun h => not_adj_both hcf hq'y.symm hty_g.symm h
      have hn2 : ¬ G.Adj (g q_idx) (g t) := fun h => not_adj_both hcf (hg q_idx y hqy.1 hqy.2).symm hty_g.symm h
      exact ⟨fun h => (hn1 h).elim, fun h => (hn2 h).elim⟩
  · have := hq' t
    simpa only [if_neg ht] using this

-- Claim 3.5: if q is adjacent to g(j + k) and g(j - k), then q is a Γ_k-twin of g(j)!
lemma claim_3_5 {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3)
    (hnoC6 : ∀ a1 a2 a3 b1 b2 b3 : V,
      G.Adj a1 b2 → G.Adj a1 b3 → G.Adj a2 b1 → G.Adj a2 b3 → G.Adj a3 b1 → G.Adj a3 b2 →
      ¬ G.Adj a1 b1 → ¬ G.Adj a2 b2 → G.Adj a3 b3)
    {k : ℕ} (hk : 1 ≤ k) (g : Fin (3 * k - 1) → V)
    (hg : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j))
    (q : V) (j : Fin (3 * k - 1))
    (hplus : G.Adj q (g ⟨(j.val + k) % (3 * k - 1), Nat.mod_lt _ (by omega)⟩))
    (hminus : G.Adj q (g ⟨(j.val + (2 * k - 1)) % (3 * k - 1), Nat.mod_lt _ (by omega)⟩)) :
    ∀ t : Fin (3 * k - 1), G.Adj q (g t) ↔ G.Adj (g j) (g t) := by
  have hM : 0 < 3 * k - 1 := by omega
  -- First show G.Adj (g j) (g t) → G.Adj q (g t) for all t
  have hsub : ∀ t : Fin (3 * k - 1),
      k ≤ (t.val + (3 * k - 1) - j.val) % (3 * k - 1) →
      (t.val + (3 * k - 1) - j.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj q (g t) := by
    intro t h1 h2
    set d := (t.val + (3 * k - 1) - j.val) % (3 * k - 1)
    by_cases hd1 : d = k
    · have ht_eq : t = ⟨(j.val + k) % (3 * k - 1), Nat.mod_lt _ hM⟩ := by
        apply Fin.ext; dsimp only
        have hrec : (j.val + d) % (3 * k - 1) = t.val := by
          dsimp only [d]
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : j.val + (t.val + (3 * k - 1) - j.val) = t.val + (3 * k - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt t.isLt]
        calc t.val = (j.val + d) % (3 * k - 1) := hrec.symm
          _ = (j.val + k) % (3 * k - 1) := by rw [hd1]
      rw [ht_eq]; exact hplus
    · by_cases hd2 : d = 2 * k - 1
      · have ht_eq : t = ⟨(j.val + (2 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩ := by
          apply Fin.ext; dsimp only
          have hrec : (j.val + d) % (3 * k - 1) = t.val := by
            dsimp only [d]
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have : j.val + (t.val + (3 * k - 1) - j.val) = t.val + (3 * k - 1) := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt t.isLt]
          calc t.val = (j.val + d) % (3 * k - 1) := hrec.symm
            _ = (j.val + (2 * k - 1)) % (3 * k - 1) := by rw [hd2]
        rw [ht_eq]; exact hminus
      · -- k < d < 2k - 1: hexagon q - p1 - s2 - t - s1 - p2 - q
        let p1 : Fin (3 * k - 1) := ⟨(j.val + k) % (3 * k - 1), Nat.mod_lt _ hM⟩
        let p2 : Fin (3 * k - 1) := ⟨(j.val + (2 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩
        let s1 : Fin (3 * k - 1) := ⟨(t.val + (2 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩
        let s2 : Fin (3 * k - 1) := ⟨(t.val + k) % (3 * k - 1), Nat.mod_lt _ hM⟩
        have hs1t_val : (t.val + (3 * k - 1) - s1.val) % (3 * k - 1) = k := by
          dsimp only [s1]
          have hshift := mod_diff_shift (M := 3 * k - 1) (x := 2 * k - 1) (y := 0) (s := t.val) (by omega) hM
          simp only [zero_add] at hshift
          have hsym : (2 * k - 1) + t.val = t.val + (2 * k - 1) := by omega
          rw [hsym, Nat.mod_eq_of_lt t.isLt] at hshift
          rw [hshift, Nat.mod_eq_of_lt (by omega)]; omega
        have hs1t : G.Adj (g s1) (g t) := hg s1 t (by omega) (by omega)
        have hs2t_val : (t.val + (3 * k - 1) - s2.val) % (3 * k - 1) = 2 * k - 1 := by
          dsimp only [s2]
          have hshift := mod_diff_shift (M := 3 * k - 1) (x := k) (y := 0) (s := t.val) (by omega) hM
          simp only [zero_add] at hshift
          have hsym : k + t.val = t.val + k := by omega
          rw [hsym, Nat.mod_eq_of_lt t.isLt] at hshift
          rw [hshift, Nat.mod_eq_of_lt (by omega)]; omega
        have hs2t : G.Adj (g s2) (g t) := hg s2 t (by omega) (by omega)
        have hp1s2 : G.Adj (g p1) (g s2) := hg p1 s2
          (by dsimp only [p1, s2]; rw [mod_diff_shift j.isLt t.isLt]; exact h1)
          (by dsimp only [p1, s2]; rw [mod_diff_shift j.isLt t.isLt]; exact h2)
        have hp2s1 : G.Adj (g p2) (g s1) := hg p2 s1
          (by dsimp only [p2, s1]; rw [mod_diff_shift j.isLt t.isLt]; exact h1)
          (by dsimp only [p2, s1]; rw [mod_diff_shift j.isLt t.isLt]; exact h2)
        have hnp1s1 : ¬ G.Adj (g p1) (g s1) := by
          apply and_twin_nonadj_of_nonadj hcf hk g hg (fun _ => Iff.rfl) (fun _ => Iff.rfl)
          have hval : (s1.val + (3 * k - 1) - p1.val) % (3 * k - 1) = d + (k - 1) := by
            dsimp only [p1]
            have hC := mod_diff_shift (M := 3 * k - 1) (x := j.val) (y := (t.val + (k - 1)) % (3 * k - 1))
              (s := k) j.isLt (Nat.mod_lt _ hM)
            have hC1 : ((t.val + (k - 1)) % (3 * k - 1) + k) % (3 * k - 1) = s1.val := by
              dsimp only [s1]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have : t.val + (k - 1) + k = t.val + (2 * k - 1) := by omega
              rw [this]
            rw [hC1] at hC
            rw [hC, mod_add_sub j.isLt]
            have : t.val + (k - 1) + (3 * k - 1) - j.val = (t.val + (3 * k - 1) - j.val) + (k - 1) := by omega
            rw [this, Nat.add_mod, Nat.mod_eq_of_lt (by omega : k - 1 < 3 * k - 1), Nat.mod_eq_of_lt (by omega)]
          omega
        have hnp2s2 : ¬ G.Adj (g p2) (g s2) := by
          apply and_twin_nonadj_of_nonadj hcf hk g hg (fun _ => Iff.rfl) (fun _ => Iff.rfl)
          have hval : (s2.val + (3 * k - 1) - p2.val) % (3 * k - 1) = d - (k - 1) := by
            dsimp only [s2]
            have hC := mod_diff_shift (M := 3 * k - 1) (x := (j.val + (k - 1)) % (3 * k - 1)) (y := t.val)
              (s := k) (Nat.mod_lt _ hM) t.isLt
            have hC1 : ((j.val + (k - 1)) % (3 * k - 1) + k) % (3 * k - 1) = p2.val := by
              dsimp only [p2]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have : j.val + (k - 1) + k = j.val + (2 * k - 1) := by omega
              rw [this]
            rw [hC1] at hC
            rw [hC]
            have hsym := mod_diff_shift (M := 3 * k - 1) (x := j.val) (y := (t.val + (3 * k - 1) - (k - 1)) % (3 * k - 1))
              (s := k - 1) j.isLt (Nat.mod_lt _ hM)
            have hsym1 : ((t.val + (3 * k - 1) - (k - 1)) % (3 * k - 1) + (k - 1)) % (3 * k - 1) = t.val := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have : t.val + (3 * k - 1) - (k - 1) + (k - 1) = t.val + (3 * k - 1) := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt t.isLt]
            rw [hsym1] at hsym
            rw [hsym, mod_add_sub j.isLt]
            have : t.val + (3 * k - 1) - (k - 1) + (3 * k - 1) - j.val = (t.val + (3 * k - 1) - j.val) + 2 * k := by omega
            rw [this, Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 * k < 3 * k - 1)]
            have hsplit : d + 2 * k = (d - (k - 1)) + (3 * k - 1) := by omega
            rw [hsplit, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          omega
        -- Hexagon: (a1, a2, a3) = (g s2, g s1, q), (b1, b2, b3) = (g p2, g p1, g t)
        exact hnoC6 (g s2) (g s1) q (g p2) (g p1) (g t)
          hp1s2.symm hs2t hp2s1.symm hs1t hminus hplus
          (fun h => hnp2s2 h.symm) (fun h => hnp1s1 h.symm)
  intro t
  by_cases hadj : k ≤ (t.val + (3 * k - 1) - j.val) % (3 * k - 1) ∧
      (t.val + (3 * k - 1) - j.val) % (3 * k - 1) ≤ 2 * k - 1
  · exact ⟨fun _ => hg j t hadj.1 hadj.2, fun _ => hsub t hadj.1 hadj.2⟩
  · obtain ⟨y, hjy, hty⟩ := and_common_neighbor hk j.isLt t.isLt hadj
    have hqy : G.Adj q (g y) := hsub y hjy.1 hjy.2
    have hty_g : G.Adj (g t) (g y) := hg t y hty.1 hty.2
    have hn1 : ¬ G.Adj q (g t) := fun h => not_adj_both hcf hqy.symm hty_g.symm h
    have hn2 : ¬ G.Adj (g j) (g t) := fun h => not_adj_both hcf (hg j y hjy.1 hjy.2).symm hty_g.symm h
    exact ⟨fun h => (hn1 h).elim, fun h => (hn2 h).elim⟩

-- Claim 3.6: if q has at least one neighbor in Γ_k, then q is a Γ_k-twin of some vertex in Γ_k!
lemma claim_3_6 {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hnoC6 : ∀ a1 a2 a3 b1 b2 b3 : V,
      G.Adj a1 b2 → G.Adj a1 b3 → G.Adj a2 b1 → G.Adj a2 b3 → G.Adj a3 b1 → G.Adj a3 b2 →
      ¬ G.Adj a1 b1 → ¬ G.Adj a2 b2 → G.Adj a3 b3)
    {k : ℕ} (hk : 1 ≤ k)
    (hnoNext : ¬ ∃ g' : Fin (3 * (k + 1) - 1) → V, ∀ i j : Fin (3 * (k + 1) - 1),
      k + 1 ≤ (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) →
      (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) ≤ 2 * (k + 1) - 1 →
      G.Adj (g' i) (g' j))
    (g : Fin (3 * k - 1) → V)
    (hg : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j))
    (q : V) (hnb : ∃ t : Fin (3 * k - 1), G.Adj q (g t)) :
    ∃ j : Fin (3 * k - 1), ∀ t : Fin (3 * k - 1), G.Adj q (g t) ↔ G.Adj (g j) (g t) := by
  have hM : 0 < 3 * k - 1 := by omega
  -- If k = 1, Γ_1 = K_2 = {0, 1}; q adj to one of them and not the other => twin of the other!
  by_cases hk1 : k = 1
  · subst hk1
    obtain ⟨t, ht⟩ := hnb
    have h01 : G.Adj (g 0) (g 1) := hg 0 1 (by decide) (by decide)
    fin_cases t
    · refine ⟨1, fun s => ?_⟩
      fin_cases s
      · exact ⟨fun _ => h01.symm, fun _ => ht⟩
      · have hnq1 : ¬ G.Adj q (g 1) := fun h => not_adj_both hcf ht h h01
        exact ⟨fun h => (hnq1 h).elim, fun h => (G.loopless.irrefl _ h).elim⟩
    · refine ⟨0, fun s => ?_⟩
      fin_cases s
      · have hnq0 : ¬ G.Adj q (g 0) := fun h => not_adj_both hcf h ht h01
        exact ⟨fun h => (hnq0 h).elim, fun h => (G.loopless.irrefl _ h).elim⟩
      · exact ⟨fun _ => h01, fun _ => ht⟩
  · have hk2 : 2 ≤ k := by omega
    -- Find i such that G.Adj q (g i) and ¬ G.Adj q (g (i - 1))
    have hnot_all : ∃ t : Fin (3 * k - 1), ¬ G.Adj q (g t) := by
      by_contra hall; push Not at hall
      have h0 : G.Adj q (g ⟨0, hM⟩) := hall ⟨0, hM⟩
      have hk_adj : G.Adj q (g ⟨k, by omega⟩) := hall ⟨k, by omega⟩
      have h0k : G.Adj (g ⟨0, hM⟩) (g ⟨k, by omega⟩) := hg ⟨0, hM⟩ ⟨k, by omega⟩
        (by dsimp only; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])
        (by dsimp only; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
      exact not_adj_both hcf h0 hk_adj h0k
    have hstep : ∃ i : Fin (3 * k - 1),
        G.Adj q (g i) ∧ ¬ G.Adj q (g ⟨(i.val + (3 * k - 1) - 1) % (3 * k - 1), Nat.mod_lt _ hM⟩) := by
      obtain ⟨t0, ht0⟩ := hnb
      obtain ⟨t1, ht1⟩ := hnot_all
      classical
      have hex : ∃ m : ℕ, ¬ G.Adj q (g ⟨(t0.val + (3 * k - 1) - m % (3 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩) := by
        refine ⟨(t0.val + (3 * k - 1) - t1.val) % (3 * k - 1), ?_⟩
        have hidx : (t0.val + (3 * k - 1) - ((t0.val + (3 * k - 1) - t1.val) % (3 * k - 1)) % (3 * k - 1)) % (3 * k - 1) = t1.val := by
          rw [Nat.mod_mod]
          by_cases h : t1.val ≤ t0.val
          · have h1 : (t0.val + (3 * k - 1) - t1.val) % (3 * k - 1) = t0.val - t1.val := by
              have : t0.val + (3 * k - 1) - t1.val = (t0.val - t1.val) + (3 * k - 1) := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [h1]
            have : t0.val + (3 * k - 1) - (t0.val - t1.val) = t1.val + (3 * k - 1) := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt t1.isLt]
          · have h1 : (t0.val + (3 * k - 1) - t1.val) % (3 * k - 1) = t0.val + (3 * k - 1) - t1.val :=
              Nat.mod_eq_of_lt (by omega)
            rw [h1]
            have : t0.val + (3 * k - 1) - (t0.val + (3 * k - 1) - t1.val) = t1.val := by omega
            rw [this, Nat.mod_eq_of_lt t1.isLt]
        have : (⟨(t0.val + (3 * k - 1) - ((t0.val + (3 * k - 1) - t1.val) % (3 * k - 1)) % (3 * k - 1)) % (3 * k - 1),
            Nat.mod_lt _ hM⟩ : Fin (3 * k - 1)) = t1 := Fin.ext hidx
        rw [this]; exact ht1
      set m := Nat.find hex
      have hm_spec : ¬ G.Adj q (g ⟨(t0.val + (3 * k - 1) - m % (3 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩) := Nat.find_spec hex
      have hm_pos : 0 < m := by
        by_contra h0; have hm0 : m = 0 := by omega
        rw [hm0] at hm_spec
        have : (⟨(t0.val + (3 * k - 1) - 0 % (3 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩ : Fin (3 * k - 1)) = t0 := by
          apply Fin.ext; simp only [Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt t0.isLt
        rw [this] at hm_spec; exact hm_spec ht0
      have hm_prev : G.Adj q (g ⟨(t0.val + (3 * k - 1) - (m - 1) % (3 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩) := by
        by_contra hnot
        exact Nat.find_min hex (by omega : m - 1 < m) hnot
      refine ⟨⟨(t0.val + (3 * k - 1) - (m - 1) % (3 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩, hm_prev, ?_⟩
      have hpred : (((t0.val + (3 * k - 1) - (m - 1) % (3 * k - 1)) % (3 * k - 1) + (3 * k - 1) - 1) % (3 * k - 1)) =
          (t0.val + (3 * k - 1) - m % (3 * k - 1)) % (3 * k - 1) := by
        rw [mod_add_sub (by omega : 1 < 3 * k - 1)]
        by_cases hwrap : (m - 1) % (3 * k - 1) = (3 * k - 1) - 1
        · have hm0 : m % (3 * k - 1) = 0 := by
            have : m = (m - 1) + 1 := by omega
            rw [this, Nat.add_mod, hwrap, Nat.mod_eq_of_lt (by omega : 1 < 3 * k - 1)]
            have : (3 * k - 1) - 1 + 1 = 3 * k - 1 := by omega
            rw [this, Nat.mod_self]
          rw [hwrap, hm0]
          have : t0.val + (3 * k - 1) - ((3 * k - 1) - 1) + (3 * k - 1) - 1 = t0.val + (3 * k - 1) := by omega
          rw [this]; simp only [Nat.sub_zero]
        · have hm1 : m % (3 * k - 1) = (m - 1) % (3 * k - 1) + 1 := by
            have hlt := Nat.mod_lt (m - 1) hM
            calc m % (3 * k - 1)
                = ((m - 1) + 1) % (3 * k - 1) := by congr 1; omega
              _ = ((m - 1) % (3 * k - 1) + 1 % (3 * k - 1)) % (3 * k - 1) := Nat.add_mod _ _ _
              _ = ((m - 1) % (3 * k - 1) + 1) % (3 * k - 1) := by rw [Nat.mod_eq_of_lt (by omega : 1 < 3 * k - 1)]
              _ = (m - 1) % (3 * k - 1) + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hm1]
          have h1 : t0.val + (3 * k - 1) - (m - 1) % (3 * k - 1) + (3 * k - 1) - 1 =
              (t0.val + (3 * k - 1) - ((m - 1) % (3 * k - 1) + 1)) + (3 * k - 1) := by
            have := Nat.mod_lt (m - 1) hM; omega
          rw [h1, Nat.add_mod_right]
      have hfin : (⟨((t0.val + (3 * k - 1) - (m - 1) % (3 * k - 1)) % (3 * k - 1) + (3 * k - 1) - 1) % (3 * k - 1),
          Nat.mod_lt _ hM⟩ : Fin (3 * k - 1)) =
          ⟨(t0.val + (3 * k - 1) - m % (3 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩ := Fin.ext hpred
      rw [hfin]; exact hm_spec
    obtain ⟨i0, hi0_adj, hi0_not⟩ := hstep
    -- Rotate g so that i0 becomes k (shift by (i0 + 2k - 1) % (3 * k - 1))!
    set sh := (i0.val + (2 * k - 1)) % (3 * k - 1)
    let gr : Fin (3 * k - 1) → V := fun t => g ⟨(t.val + sh) % (3 * k - 1), Nat.mod_lt _ hM⟩
    have hgr : ∀ a b : Fin (3 * k - 1),
        k ≤ (b.val + (3 * k - 1) - a.val) % (3 * k - 1) →
        (b.val + (3 * k - 1) - a.val) % (3 * k - 1) ≤ 2 * k - 1 →
        G.Adj (gr a) (gr b) := fun a b h1 h2 => by
      apply hg _ _
      · dsimp only; rw [mod_diff_shift a.isLt b.isLt]; exact h1
      · dsimp only; rw [mod_diff_shift a.isLt b.isLt]; exact h2
    have hgr_k : gr ⟨k, by omega⟩ = g i0 := by
      dsimp only [gr]; congr 1; apply Fin.ext
      dsimp only
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have : k + (i0.val + (2 * k - 1)) = i0.val + (3 * k - 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i0.isLt]
    have hgr_km1 : gr ⟨k - 1, by omega⟩ = g ⟨(i0.val + (3 * k - 1) - 1) % (3 * k - 1), Nat.mod_lt _ hM⟩ := by
      dsimp only [gr]; congr 1; apply Fin.ext
      dsimp only
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1; omega
    -- Reduce goal to finding a gr-twin of q (rotating back by sh gives a g-twin!)
    suffices hres : ∃ j : Fin (3 * k - 1), ∀ t : Fin (3 * k - 1), G.Adj q (gr t) ↔ G.Adj (gr j) (gr t) by
      obtain ⟨j, hj⟩ := hres
      refine ⟨⟨(j.val + sh) % (3 * k - 1), Nat.mod_lt _ hM⟩, fun t => ?_⟩
      let s : Fin (3 * k - 1) := ⟨(t.val + (3 * k - 1) - sh) % (3 * k - 1), Nat.mod_lt _ hM⟩
      have hgrs : gr s = g t := by
        dsimp only [gr, s]; congr 1; apply Fin.ext; dsimp only
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have : t.val + (3 * k - 1) - sh + sh = t.val + (3 * k - 1) := by
          have := Nat.mod_lt (i0.val + (2 * k - 1)) hM; omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt t.isLt]
      rw [← hgrs]; exact hj s
    have hqk : G.Adj q (gr ⟨k, by omega⟩) := by rw [hgr_k]; exact hi0_adj
    have hnqkm1 : ¬ G.Adj q (gr ⟨k - 1, by omega⟩) := by rw [hgr_km1]; exact hi0_not
    by_cases hq_eq : q = gr ⟨k - 1, by omega⟩
    · exact ⟨⟨k - 1, by omega⟩, fun t => by rw [hq_eq]⟩
    · obtain ⟨z, hzq, hzkm1⟩ := hmax q (gr ⟨k - 1, by omega⟩) hq_eq hnqkm1
      let v0 : Fin (3 * k - 1) := ⟨0, hM⟩
      let vk : Fin (3 * k - 1) := ⟨k, by omega⟩
      let vkm1 : Fin (3 * k - 1) := ⟨k - 1, by omega⟩
      let v2km1 : Fin (3 * k - 1) := ⟨2 * k - 1, by omega⟩
      have h0k : G.Adj (gr v0) (gr vk) := hgr v0 vk
        (by dsimp only [v0, vk]; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])
        (by dsimp only [v0, vk]; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
      have h0_2km1 : G.Adj (gr v0) (gr v2km1) := hgr v0 v2km1
        (by dsimp only [v0, v2km1]; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
        (by dsimp only [v0, v2km1]; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])
      have hkm1_2km1 : G.Adj (gr vkm1) (gr v2km1) := hgr vkm1 v2km1
        (by dsimp only [vkm1, v2km1]
            have : 2 * k - 1 + (3 * k - 1) - (k - 1) = k + (3 * k - 1) := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])
        (by dsimp only [vkm1, v2km1]
            have : 2 * k - 1 + (3 * k - 1) - (k - 1) = k + (3 * k - 1) := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
      have hnk_km1 : ¬ G.Adj (gr vk) (gr vkm1) := by
        apply and_twin_nonadj_of_nonadj hcf hk gr hgr (fun _ => Iff.rfl) (fun _ => Iff.rfl)
        dsimp only [vk, vkm1]
        have : (k - 1 + (3 * k - 1) - k) % (3 * k - 1) = (3 * k - 1) - 1 := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        omega
      -- Hexagon z - q - k - 0 - (2k-1) - (k-1) - z => G.Adj q (gr v2km1) ∨ G.Adj z (gr v0)!
      have hor : G.Adj q (gr v2km1) ∨ G.Adj z (gr v0) := by
        by_cases h1 : G.Adj q (gr v2km1)
        · exact Or.inl h1
        · right
          exact (hnoC6 (gr vkm1) q (gr v0) (gr vk) (gr v2km1) z
            hkm1_2km1 hzkm1 hqk hzq h0k h0_2km1
            (fun h => hnk_km1 h.symm) h1).symm
      rcases hor with hq2km1 | hz0
      · refine ⟨v0, claim_3_5 hcf hnoC6 hk gr hgr q v0 ?_ ?_⟩
        · convert hqk using 2; apply Fin.ext; dsimp only [v0, vk]; rw [zero_add, Nat.mod_eq_of_lt (by omega)]
        · convert hq2km1 using 2; apply Fin.ext; dsimp only [v0, v2km1]; rw [zero_add, Nat.mod_eq_of_lt (by omega)]
      · -- z is a gr-twin of v2km1!
        have hz_tw : ∀ t : Fin (3 * k - 1), G.Adj z (gr t) ↔ G.Adj (gr v2km1) (gr t) := by
          apply claim_3_5 hcf hnoC6 hk gr hgr z v2km1
          · convert hz0 using 2; apply Fin.ext; dsimp only [v0, v2km1]
            have : 2 * k - 1 + k = 3 * k - 1 := by omega
            rw [this, Nat.mod_self]
          · convert hzkm1.symm using 2; apply Fin.ext; dsimp only [vkm1, v2km1]
            have : 2 * k - 1 + (2 * k - 1) = (k - 1) + (3 * k - 1) := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        -- Replace gr v2km1 by z to form gr'
        let gr' : Fin (3 * k - 1) → V := fun t => if t = v2km1 then z else gr t
        have hgr' : ∀ a b : Fin (3 * k - 1),
            k ≤ (b.val + (3 * k - 1) - a.val) % (3 * k - 1) →
            (b.val + (3 * k - 1) - a.val) % (3 * k - 1) ≤ 2 * k - 1 →
            G.Adj (gr' a) (gr' b) := by
          intro a b h1 h2
          by_cases ha : a = v2km1
          · subst ha
            have hb : b ≠ v2km1 := fun h => by
              subst h
              have : v2km1.val + (3 * k - 1) - v2km1.val = 3 * k - 1 := by omega
              rw [this, Nat.mod_self] at h1; omega
            simp only [gr', if_pos rfl, if_neg hb]
            exact (hz_tw b).mpr (hgr v2km1 b h1 h2)
          · by_cases hb : b = v2km1
            · subst hb
              simp only [gr', if_neg ha, if_pos rfl]
              exact ((hz_tw a).mpr (hgr v2km1 a ((and_adj_symm hk a.isLt v2km1.isLt).mp ⟨h1, h2⟩).1
                ((and_adj_symm hk a.isLt v2km1.isLt).mp ⟨h1, h2⟩).2)).symm
            · simp only [gr', if_neg ha, if_neg hb]; exact hgr a b h1 h2
        have hq_tw' : ∀ t : Fin (3 * k - 1), G.Adj q (gr' t) ↔ G.Adj (gr' v0) (gr' t) := by
          apply claim_3_5 hcf hnoC6 hk gr' hgr' q v0
          · have hvk_eq : (⟨(v0.val + k) % (3 * k - 1), Nat.mod_lt _ hM⟩ : Fin (3 * k - 1)) = vk :=
              Fin.ext (by dsimp only [v0, vk]; rw [zero_add, Nat.mod_eq_of_lt (by omega)])
            rw [hvk_eq]
            simp only [gr', show vk ≠ v2km1 by intro h; have := congrArg Fin.val h; dsimp only [vk, v2km1] at this; omega, if_false]
            exact hqk
          · have hv2_eq : (⟨(v0.val + (2 * k - 1)) % (3 * k - 1), Nat.mod_lt _ hM⟩ : Fin (3 * k - 1)) = v2km1 :=
              Fin.ext (by dsimp only [v0, v2km1]; rw [zero_add, Nat.mod_eq_of_lt (by omega)])
            rw [hv2_eq]; simp only [gr', if_pos rfl]; exact hzq
        have hv0_ne : v0 ≠ v2km1 := fun h => by
          have := congrArg Fin.val h; dsimp only [v0, v2km1] at this; omega
        have hq_tw : ∀ t : Fin (3 * k - 1), G.Adj q (gr t) ↔ G.Adj (gr v0) (gr t) :=
          lemma_2_3_and hcf hmax hnoC6 hk hnoNext gr hgr hv0_ne hz_tw
            (fun t => by simpa only [gr', if_neg hv0_ne] using hq_tw' t)
        exact ⟨v0, hq_tw⟩

-- Lemma 3.4 (Attachment Lemma): EVERY vertex q ∈ V is a Γ_k-twin of some vertex in Γ_k!
lemma lemma_3_4 {V : Type} {G : SimpleGraph V}
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hnoC6 : ∀ a1 a2 a3 b1 b2 b3 : V,
      G.Adj a1 b2 → G.Adj a1 b3 → G.Adj a2 b1 → G.Adj a2 b3 → G.Adj a3 b1 → G.Adj a3 b2 →
      ¬ G.Adj a1 b1 → ¬ G.Adj a2 b2 → G.Adj a3 b3)
    {k : ℕ} (hk : 1 ≤ k)
    (hnoNext : ¬ ∃ g' : Fin (3 * (k + 1) - 1) → V, ∀ i j : Fin (3 * (k + 1) - 1),
      k + 1 ≤ (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) →
      (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) ≤ 2 * (k + 1) - 1 →
      G.Adj (g' i) (g' j))
    (g : Fin (3 * k - 1) → V)
    (hg : ∀ i j : Fin (3 * k - 1),
      k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
      (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j))
    (q : V) :
    ∃ i : Fin (3 * k - 1), ∀ t : Fin (3 * k - 1), G.Adj q (g t) ↔ G.Adj (g i) (g t) := by
  have hM : 0 < 3 * k - 1 := by omega
  by_cases hnb : ∃ t : Fin (3 * k - 1), G.Adj q (g t)
  · exact claim_3_6 hcf hmax hnoC6 hk hnoNext g hg q hnb
  · by_cases hq0 : q = g ⟨0, hM⟩
    · exact ⟨⟨0, hM⟩, fun t => by rw [hq0]⟩
    · have hnq0 : ¬ G.Adj q (g ⟨0, hM⟩) := fun h => hnb ⟨⟨0, hM⟩, h⟩
      obtain ⟨z, hzq, hz0⟩ := hmax q (g ⟨0, hM⟩) hq0 hnq0
      obtain ⟨j, hj⟩ := claim_3_6 hcf hmax hnoC6 hk hnoNext g hg z ⟨⟨0, hM⟩, hz0.symm⟩
      let g' : Fin (3 * k - 1) → V := fun t => if t = j then z else g t
      have hg' : ∀ a b : Fin (3 * k - 1),
          k ≤ (b.val + (3 * k - 1) - a.val) % (3 * k - 1) →
          (b.val + (3 * k - 1) - a.val) % (3 * k - 1) ≤ 2 * k - 1 →
          G.Adj (g' a) (g' b) := by
        intro a b h1 h2
        by_cases ha : a = j
        · have hb : b ≠ j := fun h => by
            rw [ha, h] at h1
            have : j.val + (3 * k - 1) - j.val = 3 * k - 1 := by omega
            rw [this, Nat.mod_self] at h1; omega
          simp only [g', if_pos ha, if_neg hb]; rw [ha] at h1 h2; exact (hj b).mpr (hg j b h1 h2)
        · by_cases hb : b = j
          · subst hb
            simp only [g', if_neg ha, if_pos rfl]
            exact ((hj a).mpr (hg b a ((and_adj_symm hk a.isLt b.isLt).mp ⟨h1, h2⟩).1
              ((and_adj_symm hk a.isLt b.isLt).mp ⟨h1, h2⟩).2)).symm
          · simp only [g', if_neg ha, if_neg hb]; exact hg a b h1 h2
      obtain ⟨i, hi⟩ := claim_3_6 hcf hmax hnoC6 hk hnoNext g' hg' q ⟨j, by simp only [g', if_pos rfl]; exact hzq⟩
      have hij : i ≠ j := by
        intro h; subst h
        have := (hi i).mp (by simp only [g', if_pos rfl]; exact hzq)
        exact G.loopless.irrefl _ this
      refine ⟨i, lemma_2_3_and hcf hmax hnoC6 hk hnoNext g hg hij hj ?_⟩
      intro t; simpa only [g', if_neg hij] using hi t

-- Proposition 3.7: every maximal triangle-free C_6-free graph with an edge is 3-colorable!
lemma prop_3_7_colorable3 {V : Type} [Fintype V] (G : SimpleGraph V)
    (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hedge : ∃ u v : V, G.Adj u v)
    (hnoC6 : ∀ a1 a2 a3 b1 b2 b3 : V,
      G.Adj a1 b2 → G.Adj a1 b3 → G.Adj a2 b1 → G.Adj a2 b3 → G.Adj a3 b1 → G.Adj a3 b2 →
      ¬ G.Adj a1 b1 → ¬ G.Adj a2 b2 → G.Adj a3 b3) :
    G.Colorable 3 := by
  classical
  -- Pick maximum k ≥ 1 such that Γ_k embeds into G
  have hex1 : ∃ g : Fin (3 * 1 - 1) → V, ∀ i j : Fin (3 * 1 - 1),
      1 ≤ (j.val + (3 * 1 - 1) - i.val) % (3 * 1 - 1) →
      (j.val + (3 * 1 - 1) - i.val) % (3 * 1 - 1) ≤ 2 * 1 - 1 → G.Adj (g i) (g j) := by
    obtain ⟨u, v, huv⟩ := hedge
    refine ⟨![u, v], fun i j h1 h2 => ?_⟩
    fin_cases i <;> fin_cases j <;> first | omega | exact huv | exact huv.symm
  have hbound : ∀ k : ℕ, 1 ≤ k →
      (∃ g : Fin (3 * k - 1) → V, ∀ i j : Fin (3 * k - 1),
        k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
        (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j)) →
      k ≤ Fintype.card V := by
    intro k hk ⟨g, hg⟩
    have hinj := and_hom_injective hcf hk g hg
    have hle := Fintype.card_le_of_injective g hinj
    rw [Fintype.card_fin] at hle
    omega
  -- Find maximal k ≤ card V
  have hmaxk : ∃ k : ℕ, 1 ≤ k ∧
      (∃ g : Fin (3 * k - 1) → V, ∀ i j : Fin (3 * k - 1),
        k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
        (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j)) ∧
      ¬ (∃ g' : Fin (3 * (k + 1) - 1) → V, ∀ i j : Fin (3 * (k + 1) - 1),
        k + 1 ≤ (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) →
        (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) ≤ 2 * (k + 1) - 1 → G.Adj (g' i) (g' j)) := by
    suffices h : ∀ B : ℕ, ∀ k : ℕ, 1 ≤ k → Fintype.card V - k ≤ B →
        (∃ g : Fin (3 * k - 1) → V, ∀ i j : Fin (3 * k - 1),
          k ≤ (j.val + (3 * k - 1) - i.val) % (3 * k - 1) →
          (j.val + (3 * k - 1) - i.val) % (3 * k - 1) ≤ 2 * k - 1 → G.Adj (g i) (g j)) →
        ∃ m : ℕ, 1 ≤ m ∧
          (∃ g : Fin (3 * m - 1) → V, ∀ i j : Fin (3 * m - 1),
            m ≤ (j.val + (3 * m - 1) - i.val) % (3 * m - 1) →
            (j.val + (3 * m - 1) - i.val) % (3 * m - 1) ≤ 2 * m - 1 → G.Adj (g i) (g j)) ∧
          ¬ (∃ g' : Fin (3 * (m + 1) - 1) → V, ∀ i j : Fin (3 * (m + 1) - 1),
            m + 1 ≤ (j.val + (3 * (m + 1) - 1) - i.val) % (3 * (m + 1) - 1) →
            (j.val + (3 * (m + 1) - 1) - i.val) % (3 * (m + 1) - 1) ≤ 2 * (m + 1) - 1 → G.Adj (g' i) (g' j)) from
      h (Fintype.card V) 1 (le_refl 1) (by omega) hex1
    intro B
    induction B with
    | zero =>
      intro k hk hle hex
      refine ⟨k, hk, hex, fun hex' => ?_⟩
      have := hbound (k + 1) (by omega) hex'
      omega
    | succ B ih =>
      intro k hk hle hex
      by_cases hnext : ∃ g' : Fin (3 * (k + 1) - 1) → V, ∀ i j : Fin (3 * (k + 1) - 1),
          k + 1 ≤ (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) →
          (j.val + (3 * (k + 1) - 1) - i.val) % (3 * (k + 1) - 1) ≤ 2 * (k + 1) - 1 → G.Adj (g' i) (g' j)
      · exact ih (k + 1) (by omega) (by omega) hnext
      · exact ⟨k, hk, hex, hnext⟩
  obtain ⟨k, hk, ⟨g, hg⟩, hnoNext⟩ := hmaxk
  choose φ hφ using fun q : V => lemma_3_4 hcf hmax hnoC6 hk hnoNext g hg q
  -- Compose φ with the canonical 3-coloring of Γ_k!
  refine ⟨SimpleGraph.Coloring.mk
    (fun q => if (φ q).val < k then (0 : Fin 3) else if (φ q).val < 2 * k then 1 else 2) ?_⟩
  intro x y hxy hcol
  have hnot_and : ¬ (k ≤ ((φ y).val + (3 * k - 1) - (φ x).val) % (3 * k - 1) ∧
      ((φ y).val + (3 * k - 1) - (φ x).val) % (3 * k - 1) ≤ 2 * k - 1) := by
    have hxlt := (φ x).isLt
    have hylt := (φ y).isLt
    have hdiff : ((φ y).val + (3 * k - 1) - (φ x).val) % (3 * k - 1) =
        if (φ x).val ≤ (φ y).val then (φ y).val - (φ x).val else (φ y).val + (3 * k - 1) - (φ x).val := by
      split_ifs with h
      · have : (φ y).val + (3 * k - 1) - (φ x).val = ((φ y).val - (φ x).val) + (3 * k - 1) := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · exact Nat.mod_eq_of_lt (by omega)
    rw [hdiff]
    split_ifs at hcol ⊢ <;> omega
  exact and_twin_nonadj_of_nonadj hcf hk g hg (hφ x) (hφ y) hnot_and hxy

end OMA.E128Brandt.LPR

namespace OMA.E128Brandt

open Finset SimpleGraph OMA.R_Erdos128_erdos_128_R2 OMA.R_Erdos128_erdos_128_R2_H2_R1

private abbrev HasGrotzsch {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (v u : Fin 5 → V) (w : V),
    ∀ i : Fin 5,
      G.Adj (v i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 4)) ∧
      G.Adj w (u i)

private lemma fin5_neg_add_one (i : Fin 5) : -(i + 1) = -i + 4 := by fin_cases i <;> decide
private lemma fin5_neg_add_four (i : Fin 5) : -(i + 4) = -i + 1 := by fin_cases i <;> decide

private lemma grotzsch_rot {V : Type} {G : SimpleGraph V} {v u : Fin 5 → V} {w : V}
    (hg : ∀ i : Fin 5,
      G.Adj (v i) (v (i + 1)) ∧ G.Adj (u i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 4)) ∧ G.Adj w (u i)) (r : Fin 5) :
    ∀ i : Fin 5,
      G.Adj (v (i + r)) (v ((i + 1) + r)) ∧
      G.Adj (u (i + r)) (v ((i + 1) + r)) ∧
      G.Adj (u (i + r)) (v ((i + 4) + r)) ∧
      G.Adj w (u (i + r)) := by
  intro i
  have h := hg (i + r)
  have h1 : i + r + 1 = i + 1 + r := by fin_cases i <;> fin_cases r <;> decide
  have h4 : i + r + 4 = i + 4 + r := by fin_cases i <;> fin_cases r <;> decide
  rw [h1, h4] at h
  exact h

private lemma grotzsch_rev {V : Type} {G : SimpleGraph V} {v u : Fin 5 → V} {w : V}
    (hg : ∀ i : Fin 5,
      G.Adj (v i) (v (i + 1)) ∧ G.Adj (u i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 4)) ∧ G.Adj w (u i)) :
    ∀ i : Fin 5,
      G.Adj (v (-i)) (v (-(i + 1))) ∧
      G.Adj (u (-i)) (v (-(i + 1))) ∧
      G.Adj (u (-i)) (v (-(i + 4))) ∧
      G.Adj w (u (-i)) := by
  intro i
  refine ⟨?_, ?_, ?_, (hg (-i)).2.2.2⟩
  · have h := (hg (-(i + 1))).1.symm
    rwa [fin5_neg_add] at h
  · rw [fin5_neg_add_one]
    exact (hg (-i)).2.2.1
  · rw [fin5_neg_add_four]
    exact (hg (-i)).2.1

private lemma grotzsch_v_ne_v {V : Type} {H : SimpleGraph V} (hcf : H.CliqueFree 3)
    {v u : Fin 5 → V} {w : V}
    (hg : ∀ i : Fin 5,
      H.Adj (v i) (v (i + 1)) ∧ H.Adj (u i) (v (i + 1)) ∧
      H.Adj (u i) (v (i + 4)) ∧ H.Adj w (u i))
    {i j : Fin 5} (hij : i ≠ j) : v i ≠ v j := by
  intro heq
  rcases fin5_cases_rel i j with rfl | rfl | rfl | rfl | rfl
  · exact hij rfl
  · exact H.ne_of_adj (hg i).1 heq
  · have h1 : H.Adj (v i) (v (i + 4)) := by
      have h := (hg (i + 4)).1.symm; rwa [fin5_add_4_1] at h
    have h2 : H.Adj (v (i + 2)) (v (i + 3)) := by
      have h := (hg (i + 2)).1; rwa [fin5_add_2_1] at h
    have h3 : H.Adj (v (i + 3)) (v (i + 4)) := by
      have h := (hg (i + 3)).1; rwa [fin5_add_3_1] at h
    rw [heq] at h1
    exact not_adj_both_of_cliqueFree hcf h2 h1 h3
  · have h1 : H.Adj (v i) (v (i + 1)) := (hg i).1
    have h2 : H.Adj (v (i + 3)) (v (i + 2)) := by
      have h := (hg (i + 2)).1.symm; rwa [fin5_add_2_1] at h
    have h3 : H.Adj (v (i + 1)) (v (i + 2)) := by
      have h := (hg (i + 1)).1; rwa [fin5_add_1_1] at h
    rw [heq] at h1
    exact not_adj_both_of_cliqueFree hcf h1 h2 h3
  · have h := (hg (i + 4)).1.symm
    rw [fin5_add_4_1] at h
    exact H.ne_of_adj h heq

private lemma grotzsch_v_ne_u {V : Type} {H : SimpleGraph V} (hcf : H.CliqueFree 3)
    {v u : Fin 5 → V} {w : V}
    (hg : ∀ i : Fin 5,
      H.Adj (v i) (v (i + 1)) ∧ H.Adj (u i) (v (i + 1)) ∧
      H.Adj (u i) (v (i + 4)) ∧ H.Adj w (u i))
    (i j : Fin 5) : v i ≠ u j := by
  intro heq
  rcases fin5_cases_rel i j with rfl | rfl | rfl | rfl | rfl
  · have h1 : H.Adj (v j) (u (j + 1)) := by
      have h := (hg (j + 1)).2.2.1.symm; rwa [fin5_add_1_4] at h
    have h2 : H.Adj (u j) w := (hg j).2.2.2.symm
    have h3 : H.Adj w (u (j + 1)) := (hg (j + 1)).2.2.2
    rw [heq] at h1
    exact not_adj_both_of_cliqueFree hcf h2 h1 h3
  · have h := (hg (i + 1)).2.2.1.symm
    rw [fin5_add_1_4] at h
    exact H.ne_of_adj h heq
  · have h1 : H.Adj (v i) (v (i + 4)) := by
      have h := (hg (i + 4)).1.symm; rwa [fin5_add_4_1] at h
    have h2 : H.Adj (u (i + 2)) (v (i + 3)) := by
      have h := (hg (i + 2)).2.1; rwa [fin5_add_2_1] at h
    have h3 : H.Adj (v (i + 3)) (v (i + 4)) := by
      have h := (hg (i + 3)).1; rwa [fin5_add_3_1] at h
    rw [heq] at h1
    exact not_adj_both_of_cliqueFree hcf h2 h1 h3
  · have h1 : H.Adj (v i) (v (i + 1)) := (hg i).1
    have h2 : H.Adj (u (i + 3)) (v (i + 2)) := by
      have h := (hg (i + 3)).2.2.1; rwa [fin5_add_3_4] at h
    have h3 : H.Adj (v (i + 1)) (v (i + 2)) := by
      have h := (hg (i + 1)).1; rwa [fin5_add_1_1] at h
    rw [heq] at h1
    exact not_adj_both_of_cliqueFree hcf h1 h2 h3
  · have h := (hg (i + 4)).2.1.symm
    rw [fin5_add_4_1] at h
    exact H.ne_of_adj h heq

private lemma grotzsch_v_ne_w {V : Type} {H : SimpleGraph V} (hcf : H.CliqueFree 3)
    {v u : Fin 5 → V} {w : V}
    (hg : ∀ i : Fin 5,
      H.Adj (v i) (v (i + 1)) ∧ H.Adj (u i) (v (i + 1)) ∧
      H.Adj (u i) (v (i + 4)) ∧ H.Adj w (u i))
    (i : Fin 5) : v i ≠ w := by
  intro heq
  have h1 : H.Adj (v i) (v (i + 1)) := (hg i).1
  have h2 : H.Adj w (u i) := (hg i).2.2.2
  have h3 : H.Adj (u i) (v (i + 1)) := (hg i).2.1
  rw [heq] at h1
  exact not_adj_both_of_cliqueFree hcf h2 h1 h3

private lemma grotzsch_u_ne_u {V : Type} {H : SimpleGraph V} (hcf : H.CliqueFree 3)
    {v u : Fin 5 → V} {w : V}
    (hg : ∀ i : Fin 5,
      H.Adj (v i) (v (i + 1)) ∧ H.Adj (u i) (v (i + 1)) ∧
      H.Adj (u i) (v (i + 4)) ∧ H.Adj w (u i))
    {i j : Fin 5} (hij : i ≠ j) : u i ≠ u j := by
  intro heq
  rcases fin5_cases_rel i j with rfl | rfl | rfl | rfl | rfl
  · exact hij rfl
  · have h1 : H.Adj (u i) (v (i + 1)) := (hg i).2.1
    have h2 : H.Adj (u (i + 1)) (v (i + 2)) := by
      have h := (hg (i + 1)).2.1; rwa [fin5_add_1_1] at h
    have h3 : H.Adj (v (i + 1)) (v (i + 2)) := by
      have h := (hg (i + 1)).1; rwa [fin5_add_1_1] at h
    rw [heq] at h1
    exact not_adj_both_of_cliqueFree hcf h1 h2 h3
  · have h1 : H.Adj (u i) (v (i + 4)) := (hg i).2.2.1
    have h2 : H.Adj (u (i + 2)) (v (i + 3)) := by
      have h := (hg (i + 2)).2.1; rwa [fin5_add_2_1] at h
    have h3 : H.Adj (v (i + 3)) (v (i + 4)) := by
      have h := (hg (i + 3)).1; rwa [fin5_add_3_1] at h
    rw [heq] at h1
    exact not_adj_both_of_cliqueFree hcf h2 h1 h3
  · have h1 : H.Adj (u i) (v (i + 1)) := (hg i).2.1
    have h2 : H.Adj (u (i + 3)) (v (i + 2)) := by
      have h := (hg (i + 3)).2.2.1; rwa [fin5_add_3_4] at h
    have h3 : H.Adj (v (i + 1)) (v (i + 2)) := by
      have h := (hg (i + 1)).1; rwa [fin5_add_1_1] at h
    rw [heq] at h1
    exact not_adj_both_of_cliqueFree hcf h1 h2 h3
  · have h1 : H.Adj (u i) (v (i + 4)) := (hg i).2.2.1
    have h2 : H.Adj (u (i + 4)) (v (i + 3)) := by
      have h := (hg (i + 4)).2.2.1; rwa [fin5_add_4_4] at h
    have h3 : H.Adj (v (i + 3)) (v (i + 4)) := by
      have h := (hg (i + 3)).1; rwa [fin5_add_3_1] at h
    rw [heq] at h1
    exact not_adj_both_of_cliqueFree hcf h2 h1 h3

private lemma grotzsch_u_ne_w {V : Type} {H : SimpleGraph V}
    {v u : Fin 5 → V} {w : V}
    (hg : ∀ i : Fin 5,
      H.Adj (v i) (v (i + 1)) ∧ H.Adj (u i) (v (i + 1)) ∧
      H.Adj (u i) (v (i + 4)) ∧ H.Adj w (u i))
    (i : Fin 5) : u i ≠ w :=
  H.ne_of_adj (hg i).2.2.2.symm

/- ### Three-Orbit Exact Integer Dual Inequalities -/

private lemma dual_v0v1 (v0 v1 v2 v3 v4 u0 u1 u2 u3 u4 w : Bool)
    (hv01 : (!(v0 && v1)) = true) (hv12 : (!(v1 && v2)) = true) (hv23 : (!(v2 && v3)) = true)
    (hv34 : (!(v3 && v4)) = true) (hv40 : (!(v4 && v0)) = true)
    (hu01 : (!(u0 && v1)) = true) (hu04 : (!(u0 && v4)) = true) (hw0 : (!(w && u0)) = true)
    (hu12 : (!(u1 && v2)) = true) (hu10 : (!(u1 && v0)) = true) (hw1 : (!(w && u1)) = true)
    (hu23 : (!(u2 && v3)) = true) (hu21 : (!(u2 && v1)) = true) (hw2 : (!(w && u2)) = true)
    (hu34 : (!(u3 && v4)) = true) (hu32 : (!(u3 && v2)) = true) (hw3 : (!(w && u3)) = true)
    (hu40 : (!(u4 && v0)) = true) (hu43 : (!(u4 && v3)) = true) (hw4 : (!(w && u4)) = true)
    (hno0 : ¬ (v1 = true ∧ v4 = true ∧ u1 = true ∧ u4 = true))
    (hno1 : ¬ (v0 = true ∧ v2 = true ∧ u0 = true ∧ u2 = true)) :
    v0.toNat + v1.toNat + v2.toNat + v3.toNat + v4.toNat +
    u0.toNat + u1.toNat + u4.toNat + w.toNat ≤ 3 := by
  have c0 := bool_toNat_le_one u0; have c1 := bool_toNat_le_one u1
  have c4 := bool_toNat_le_one u4
  cases w
  · rcases c5_cases v0 v1 v2 v3 v4 hv01 hv12 hv23 hv34 hv40 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu40; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu12; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu43; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu04; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01
      cases u1 <;> cases u4 <;>
        first | (simp only [Bool.toNat_true, Bool.toNat_false]; omega) | exact (hno0 ⟨rfl, rfl, rfl, rfl⟩).elim
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu40; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu43; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu04; have := bool_zero_of_pair rfl hu12; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu40; simp only [Bool.toNat_true, Bool.toNat_false]; omega
  · have := bool_zero_of_pair' hw0; have := bool_zero_of_pair' hw1
    have := bool_zero_of_pair' hw4
    have e01 := bool_pair_le_one hv01; have e12 := bool_pair_le_one hv12
    have e23 := bool_pair_le_one hv23; have e34 := bool_pair_le_one hv34
    have e40 := bool_pair_le_one hv40
    simp only [Bool.toNat_true]; omega

private lemma dual_u0v1 (v0 v1 v2 v3 v4 u0 u1 u2 u3 u4 w : Bool)
    (hv01 : (!(v0 && v1)) = true) (hv12 : (!(v1 && v2)) = true) (hv23 : (!(v2 && v3)) = true)
    (hv34 : (!(v3 && v4)) = true) (hv40 : (!(v4 && v0)) = true)
    (hu01 : (!(u0 && v1)) = true) (hu04 : (!(u0 && v4)) = true) (hw0 : (!(w && u0)) = true)
    (hu12 : (!(u1 && v2)) = true) (hu10 : (!(u1 && v0)) = true) (hw1 : (!(w && u1)) = true)
    (hu23 : (!(u2 && v3)) = true) (hu21 : (!(u2 && v1)) = true) (hw2 : (!(w && u2)) = true)
    (hu34 : (!(u3 && v4)) = true) (hu32 : (!(u3 && v2)) = true) (hw3 : (!(w && u3)) = true)
    (hu40 : (!(u4 && v0)) = true) (hu43 : (!(u4 && v3)) = true) (hw4 : (!(w && u4)) = true)
    (hno0 : ¬ (v1 = true ∧ v4 = true ∧ w = true))
    (hno1 : ¬ (v0 = true ∧ v2 = true ∧ u0 = true ∧ u2 = true)) :
    v0.toNat + v1.toNat + v2.toNat + v3.toNat + v4.toNat +
    u0.toNat + u1.toNat + u2.toNat + w.toNat ≤ 3 := by
  have c0 := bool_toNat_le_one u0; have c1 := bool_toNat_le_one u1
  have c2 := bool_toNat_le_one u2
  cases w
  · rcases c5_cases v0 v1 v2 v3 v4 hv01 hv12 hv23 hv34 hv40 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp only [Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu21; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu12; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu23; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu04; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu21; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10
      cases u0 <;> cases u2 <;>
        first | (simp only [Bool.toNat_true, Bool.toNat_false]; omega) | exact (hno1 ⟨rfl, rfl, rfl, rfl⟩).elim
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu21; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu04; have := bool_zero_of_pair rfl hu12; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu23; simp only [Bool.toNat_true, Bool.toNat_false]; omega
  · have := bool_zero_of_pair' hw0; have := bool_zero_of_pair' hw1
    have := bool_zero_of_pair' hw2
    have e01 := bool_pair_le_one hv01; have e12 := bool_pair_le_one hv12
    have e23 := bool_pair_le_one hv23; have e34 := bool_pair_le_one hv34
    have e40 := bool_pair_le_one hv40
    simp only [Bool.toNat_true]; omega

private lemma dual_wu0 (v0 v1 v2 v3 v4 u0 u1 u2 u3 u4 w : Bool)
    (hv01 : (!(v0 && v1)) = true) (hv12 : (!(v1 && v2)) = true) (hv23 : (!(v2 && v3)) = true)
    (hv34 : (!(v3 && v4)) = true) (hv40 : (!(v4 && v0)) = true)
    (hu01 : (!(u0 && v1)) = true) (hu04 : (!(u0 && v4)) = true) (hw0 : (!(w && u0)) = true)
    (hu12 : (!(u1 && v2)) = true) (hu10 : (!(u1 && v0)) = true) (hw1 : (!(w && u1)) = true)
    (hu23 : (!(u2 && v3)) = true) (hu21 : (!(u2 && v1)) = true) (hw2 : (!(w && u2)) = true)
    (hu34 : (!(u3 && v4)) = true) (hu32 : (!(u3 && v2)) = true) (hw3 : (!(w && u3)) = true)
    (hu40 : (!(u4 && v0)) = true) (hu43 : (!(u4 && v3)) = true) (hw4 : (!(w && u4)) = true)
    (hnow : ¬ (u0 = true ∧ u1 = true ∧ u2 = true ∧ u3 = true ∧ u4 = true))
    (hno0 : ¬ (v1 = true ∧ v4 = true ∧ w = true)) :
    v0.toNat + v1.toNat + v2.toNat + v3.toNat + v4.toNat +
    u0.toNat + u1.toNat + u2.toNat + u3.toNat + u4.toNat + 2 * w.toNat ≤ 4 := by
  have c0 := bool_toNat_le_one u0; have c1 := bool_toNat_le_one u1
  have c2 := bool_toNat_le_one u2; have c3 := bool_toNat_le_one u3
  have c4 := bool_toNat_le_one u4
  cases w
  · rcases c5_cases v0 v1 v2 v3 v4 hv01 hv12 hv23 hv34 hv40 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · cases u0 <;> cases u1 <;> cases u2 <;> cases u3 <;> cases u4 <;>
        first | decide | exact (hnow ⟨rfl, rfl, rfl, rfl, rfl⟩).elim
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu40; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu21; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu12; have := bool_zero_of_pair rfl hu32; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu23; have := bool_zero_of_pair rfl hu43; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu04; have := bool_zero_of_pair rfl hu34; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu21; have := bool_zero_of_pair rfl hu34; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu32; have := bool_zero_of_pair rfl hu40; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu01; have := bool_zero_of_pair rfl hu21; have := bool_zero_of_pair rfl hu43; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu04; have := bool_zero_of_pair rfl hu12; have := bool_zero_of_pair rfl hu32; simp only [Bool.toNat_true, Bool.toNat_false]; omega
    · have := bool_zero_of_pair rfl hu10; have := bool_zero_of_pair rfl hu23; have := bool_zero_of_pair rfl hu40; simp only [Bool.toNat_true, Bool.toNat_false]; omega
  · have := bool_zero_of_pair' hw0; have := bool_zero_of_pair' hw1
    have := bool_zero_of_pair' hw2; have := bool_zero_of_pair' hw3
    have := bool_zero_of_pair' hw4
    have e01 := bool_pair_le_one hv01; have e12 := bool_pair_le_one hv12
    have e23 := bool_pair_le_one hv23; have e34 := bool_pair_le_one hv34
    have e40 := bool_pair_le_one hv40
    simp only [Bool.toNat_true]; omega

private lemma sum_decide_toNat {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) :
    (∑ x : V, (decide (G.Adj x z)).toNat) = (G.neighborSet z).ncard := by
  rw [← sum_adj_eq_neighborSet_ncard G z]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (bool_ite_eq_toNat _).symm

private lemma nine_lt_contra {n a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℕ}
    (h0 : n < 3 * a0) (h1 : n < 3 * a1) (h2 : n < 3 * a2)
    (h3 : n < 3 * a3) (h4 : n < 3 * a4) (h5 : n < 3 * a5)
    (h6 : n < 3 * a6) (h7 : n < 3 * a7) (h8 : n < 3 * a8)
    (hle : a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 ≤ 3 * n) : False := by
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, hle]

private lemma twelve_lt_contra {n a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℕ}
    (h0 : n < 3 * a0) (h1 : n < 3 * a1) (h2 : n < 3 * a2)
    (h3 : n < 3 * a3) (h4 : n < 3 * a4) (h5 : n < 3 * a5)
    (h6 : n < 3 * a6) (h7 : n < 3 * a7) (h8 : n < 3 * a8)
    (h9 : n < 3 * a9) (h10 : n < 3 * a10)
    (hle : a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + 2 * a10 ≤ 4 * n) : False := by
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hle]

private lemma edge_other {V : Type} {G H : SimpleGraph V} {x y a b p q : V}
    (hH_adj : ∀ u v : V, H.Adj u v ↔ G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (hab : H.Adj a b) (hnab : ¬ G.Adj a b) (hpq : H.Adj p q)
    (h1 : ¬ (p = a ∧ q = b)) (h2 : ¬ (p = b ∧ q = a)) : G.Adj p q := by
  have hab' := (hH_adj a b).mp hab
  have hpq' := (hH_adj p q).mp hpq
  rcases hab' with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hnab h).elim
  · rcases hpq' with h | h | h
    · exact h
    · exact (h1 h).elim
    · exact (h2 h).elim
  · rcases hpq' with h | h | h
    · exact h
    · exact (h2 h).elim
    · exact (h1 h).elim

private lemma grotzsch_sub_profile {V : Type} {G H : SimpleGraph V} [DecidableRel G.Adj]
    (hGH : G ≤ H) (hHcf : H.CliqueFree 3)
    (v' u' : Fin 5 → V) (w' : V)
    (hg' : ∀ i : Fin 5, H.Adj (v' i) (v' (i + 1)) ∧ H.Adj (u' i) (v' (i + 1)) ∧
      H.Adj (u' i) (v' (i + 4)) ∧ H.Adj w' (u' i)) (z : V) :
    ∀ i : Fin 5,
      !(decide (G.Adj z (v' i)) && decide (G.Adj z (v' (i + 1)))) ∧
      !(decide (G.Adj z (u' i)) && decide (G.Adj z (v' (i + 1)))) ∧
      !(decide (G.Adj z (u' i)) && decide (G.Adj z (v' (i + 4)))) ∧
      !(decide (G.Adj z w') && decide (G.Adj z (u' i))) := by
  intro i
  obtain ⟨h1, h2, h3, h4⟩ := hg' i
  exact ⟨not_and_decide fun ha hb => not_adj_both_of_cliqueFree hHcf (hGH ha) (hGH hb) h1,
         not_and_decide fun ha hb => not_adj_both_of_cliqueFree hHcf (hGH ha) (hGH hb) h2,
         not_and_decide fun ha hb => not_adj_both_of_cliqueFree hHcf (hGH ha) (hGH hb) h3,
         not_and_decide fun ha hb => not_adj_both_of_cliqueFree hHcf (hGH ha) (hGH hb) h4⟩

private lemma orbit_vv_contra {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ z : V, Fintype.card V < 3 * (G.neighborSet z).ncard)
    (hnoG : ¬ HasGrotzsch G)
    {x y : V} (hGH : G ≤ H) (hHcf : H.CliqueFree 3)
    (hH_adj : ∀ a b : V, H.Adj a b ↔ G.Adj a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (v' u' : Fin 5 → V) (w' : V)
    (hg' : ∀ i : Fin 5, H.Adj (v' i) (v' (i + 1)) ∧ H.Adj (u' i) (v' (i + 1)) ∧
      H.Adj (u' i) (v' (i + 4)) ∧ H.Adj w' (u' i))
    (hnot : ¬ G.Adj (v' 0) (v' 1)) : False := by
  have hvv : ∀ {i j : Fin 5}, i ≠ j → v' i ≠ v' j := fun hij => grotzsch_v_ne_v hHcf hg' hij
  have hvu := grotzsch_v_ne_u hHcf hg'
  have hvw := grotzsch_v_ne_w hHcf hg'
  have hno0 : ∀ z : V, ¬ (G.Adj z (v' 1) ∧ G.Adj z (v' 4) ∧ G.Adj z (u' 1) ∧ G.Adj z (u' 4)) := by
    rintro z ⟨hz1, hz4, hzu1, hzu4⟩
    apply hnoG
    refine ⟨fun i => if i = 0 then z else v' i, u', w', fun i => ?_⟩
    fin_cases i
    · exact ⟨hz1,
        edge_other hH_adj (hg' 0).1 hnot (hg' 0).2.1 (fun h => hvu 0 0 h.1.symm) (fun h => hvu 1 0 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 0).2.2.1 (fun h => hvu 0 0 h.1.symm) (fun h => hvu 1 0 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 0).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).1 hnot (hg' 1).1 (fun h => hvv (i := 0) (j := 1) (by decide) h.1.symm) (fun h => hvv (i := 0) (j := 2) (by decide) h.2.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 1).2.1 (fun h => hvu 0 1 h.1.symm) (fun h => hvu 1 1 h.1.symm),
        hzu1.symm,
        edge_other hH_adj (hg' 0).1 hnot (hg' 1).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).1 hnot (hg' 2).1 (fun h => hvv (i := 0) (j := 2) (by decide) h.1.symm) (fun h => hvv (i := 1) (j := 2) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 2).2.1 (fun h => hvu 0 2 h.1.symm) (fun h => hvu 1 2 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 2).2.2.1 (fun h => hvu 0 2 h.1.symm) (fun h => hvu 1 2 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 2).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).1 hnot (hg' 3).1 (fun h => hvv (i := 0) (j := 3) (by decide) h.1.symm) (fun h => hvv (i := 1) (j := 3) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 3).2.1 (fun h => hvu 0 3 h.1.symm) (fun h => hvu 1 3 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 3).2.2.1 (fun h => hvu 0 3 h.1.symm) (fun h => hvu 1 3 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 3).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨hz4.symm, hzu4.symm,
        edge_other hH_adj (hg' 0).1 hnot (hg' 4).2.2.1 (fun h => hvu 0 4 h.1.symm) (fun h => hvu 1 4 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 4).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
  have hno1 : ∀ z : V, ¬ (G.Adj z (v' 0) ∧ G.Adj z (v' 2) ∧ G.Adj z (u' 0) ∧ G.Adj z (u' 2)) := by
    rintro z ⟨hz0, hz2, hzu0, hzu2⟩
    apply hnoG
    refine ⟨fun i => if i = 1 then z else v' i, u', w', fun i => ?_⟩
    fin_cases i
    · exact ⟨hz0.symm, hzu0.symm,
        edge_other hH_adj (hg' 0).1 hnot (hg' 0).2.2.1 (fun h => hvu 0 0 h.1.symm) (fun h => hvu 1 0 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 0).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨hz2,
        edge_other hH_adj (hg' 0).1 hnot (hg' 1).2.1 (fun h => hvu 0 1 h.1.symm) (fun h => hvu 1 1 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 1).2.2.1 (fun h => hvu 0 1 h.1.symm) (fun h => hvu 1 1 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 1).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).1 hnot (hg' 2).1 (fun h => hvv (i := 0) (j := 2) (by decide) h.1.symm) (fun h => hvv (i := 1) (j := 2) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 2).2.1 (fun h => hvu 0 2 h.1.symm) (fun h => hvu 1 2 h.1.symm),
        hzu2.symm,
        edge_other hH_adj (hg' 0).1 hnot (hg' 2).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).1 hnot (hg' 3).1 (fun h => hvv (i := 0) (j := 3) (by decide) h.1.symm) (fun h => hvv (i := 1) (j := 3) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 3).2.1 (fun h => hvu 0 3 h.1.symm) (fun h => hvu 1 3 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 3).2.2.1 (fun h => hvu 0 3 h.1.symm) (fun h => hvu 1 3 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 3).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).1 hnot (hg' 4).1 (fun h => hvv (i := 0) (j := 4) (by decide) h.1.symm) (fun h => hvv (i := 1) (j := 4) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 4).2.1 (fun h => hvu 0 4 h.1.symm) (fun h => hvu 1 4 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 4).2.2.1 (fun h => hvu 0 4 h.1.symm) (fun h => hvu 1 4 h.1.symm),
        edge_other hH_adj (hg' 0).1 hnot (hg' 4).2.2.2 (fun h => hvw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
  have hsum_le :
      (G.neighborSet (v' 0)).ncard + (G.neighborSet (v' 1)).ncard + (G.neighborSet (v' 2)).ncard +
      (G.neighborSet (v' 3)).ncard + (G.neighborSet (v' 4)).ncard +
      (G.neighborSet (u' 0)).ncard + (G.neighborSet (u' 1)).ncard + (G.neighborSet (u' 4)).ncard +
      (G.neighborSet w').ncard ≤ 3 * Fintype.card V := by
    rw [← sum_decide_toNat G (v' 0), ← sum_decide_toNat G (v' 1), ← sum_decide_toNat G (v' 2),
        ← sum_decide_toNat G (v' 3), ← sum_decide_toNat G (v' 4),
        ← sum_decide_toNat G (u' 0), ← sum_decide_toNat G (u' 1), ← sum_decide_toNat G (u' 4),
        ← sum_decide_toNat G w']
    simp only [← Finset.sum_add_distrib]
    calc _ ≤ ∑ _z : V, (3 : ℕ) := Finset.sum_le_sum fun z _ => by
          have p := grotzsch_sub_profile hGH hHcf v' u' w' hg' z
          have p0 := p 0; have p1 := p 1; have p2 := p 2; have p3 := p 3; have p4 := p 4
          simp only [Fin.reduceAdd] at p0 p1 p2 p3 p4
          exact dual_v0v1
            (decide (G.Adj z (v' 0))) (decide (G.Adj z (v' 1))) (decide (G.Adj z (v' 2)))
            (decide (G.Adj z (v' 3))) (decide (G.Adj z (v' 4)))
            (decide (G.Adj z (u' 0))) (decide (G.Adj z (u' 1))) (decide (G.Adj z (u' 2)))
            (decide (G.Adj z (u' 3))) (decide (G.Adj z (u' 4))) (decide (G.Adj z w'))
            p0.1 p1.1 p2.1 p3.1 p4.1
            p0.2.1 p0.2.2.1 p0.2.2.2 p1.2.1 p1.2.2.1 p1.2.2.2
            p2.2.1 p2.2.2.1 p2.2.2.2 p3.2.1 p3.2.2.1 p3.2.2.2
            p4.2.1 p4.2.2.1 p4.2.2.2
            (fun ⟨a, b, c, d⟩ => hno0 z ⟨of_decide_eq_true a, of_decide_eq_true b, of_decide_eq_true c, of_decide_eq_true d⟩)
            (fun ⟨a, b, c, d⟩ => hno1 z ⟨of_decide_eq_true a, of_decide_eq_true b, of_decide_eq_true c, of_decide_eq_true d⟩)
      _ = 3 * Fintype.card V := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  exact nine_lt_contra (hmin (v' 0)) (hmin (v' 1)) (hmin (v' 2)) (hmin (v' 3)) (hmin (v' 4))
    (hmin (u' 0)) (hmin (u' 1)) (hmin (u' 4)) (hmin w') hsum_le

private lemma orbit_uv_contra {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ z : V, Fintype.card V < 3 * (G.neighborSet z).ncard)
    (hnoG : ¬ HasGrotzsch G)
    {x y : V} (hGH : G ≤ H) (hHcf : H.CliqueFree 3)
    (hH_adj : ∀ a b : V, H.Adj a b ↔ G.Adj a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (v' u' : Fin 5 → V) (w' : V)
    (hg' : ∀ i : Fin 5, H.Adj (v' i) (v' (i + 1)) ∧ H.Adj (u' i) (v' (i + 1)) ∧
      H.Adj (u' i) (v' (i + 4)) ∧ H.Adj w' (u' i))
    (hnot : ¬ G.Adj (u' 0) (v' 1)) : False := by
  have hvv : ∀ {i j : Fin 5}, i ≠ j → v' i ≠ v' j := fun hij => grotzsch_v_ne_v hHcf hg' hij
  have hvu := grotzsch_v_ne_u hHcf hg'
  have hvw := grotzsch_v_ne_w hHcf hg'
  have huu : ∀ {i j : Fin 5}, i ≠ j → u' i ≠ u' j := fun hij => grotzsch_u_ne_u hHcf hg' hij
  have huw := grotzsch_u_ne_w hg'
  have hno0 : ∀ z : V, ¬ (G.Adj z (v' 1) ∧ G.Adj z (v' 4) ∧ G.Adj z w') := by
    rintro z ⟨hz1, hz4, hzw⟩
    apply hnoG
    refine ⟨v', fun i => if i = 0 then z else u' i, w', fun i => ?_⟩
    fin_cases i
    · exact ⟨edge_other hH_adj (hg' 0).2.1 hnot (hg' 0).1 (fun h => hvu 0 0 h.1) (fun h => hvv (i := 0) (j := 1) (by decide) h.1),
        hz1, hz4, hzw.symm⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.1 hnot (hg' 1).1 (fun h => hvu 1 0 h.1) (fun h => hvu 2 0 h.2),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 1).2.1 (fun h => huu (i := 0) (j := 1) (by decide) h.1.symm) (fun h => hvu 1 1 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 1).2.2.1 (fun h => huu (i := 0) (j := 1) (by decide) h.1.symm) (fun h => hvu 1 1 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 1).2.2.2 (fun h => huw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.1 hnot (hg' 2).1 (fun h => hvu 2 0 h.1) (fun h => hvv (i := 1) (j := 2) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 2).2.1 (fun h => huu (i := 0) (j := 2) (by decide) h.1.symm) (fun h => hvu 1 2 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 2).2.2.1 (fun h => huu (i := 0) (j := 2) (by decide) h.1.symm) (fun h => hvu 1 2 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 2).2.2.2 (fun h => huw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.1 hnot (hg' 3).1 (fun h => hvu 3 0 h.1) (fun h => hvv (i := 1) (j := 3) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 3).2.1 (fun h => huu (i := 0) (j := 3) (by decide) h.1.symm) (fun h => hvu 1 3 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 3).2.2.1 (fun h => huu (i := 0) (j := 3) (by decide) h.1.symm) (fun h => hvu 1 3 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 3).2.2.2 (fun h => huw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.1 hnot (hg' 4).1 (fun h => hvu 4 0 h.1) (fun h => hvv (i := 1) (j := 4) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 4).2.1 (fun h => huu (i := 0) (j := 4) (by decide) h.1.symm) (fun h => hvu 1 4 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 4).2.2.1 (fun h => huu (i := 0) (j := 4) (by decide) h.1.symm) (fun h => hvu 1 4 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 4).2.2.2 (fun h => huw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
  have hno1 : ∀ z : V, ¬ (G.Adj z (v' 0) ∧ G.Adj z (v' 2) ∧ G.Adj z (u' 0) ∧ G.Adj z (u' 2)) := by
    rintro z ⟨hz0, hz2, hzu0, hzu2⟩
    apply hnoG
    refine ⟨fun i => if i = 1 then z else v' i, u', w', fun i => ?_⟩
    fin_cases i
    · exact ⟨hz0.symm, hzu0.symm,
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 0).2.2.1 (fun h => hvv (i := 1) (j := 4) (by decide) h.2.symm) (fun h => hvu 1 0 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 0).2.2.2 (fun h => huw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨hz2,
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 1).2.1 (fun h => huu (i := 0) (j := 1) (by decide) h.1.symm) (fun h => hvu 1 1 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 1).2.2.1 (fun h => huu (i := 0) (j := 1) (by decide) h.1.symm) (fun h => hvu 1 1 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 1).2.2.2 (fun h => huw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.1 hnot (hg' 2).1 (fun h => hvu 2 0 h.1) (fun h => hvv (i := 1) (j := 2) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 2).2.1 (fun h => huu (i := 0) (j := 2) (by decide) h.1.symm) (fun h => hvu 1 2 h.1.symm),
        hzu2.symm,
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 2).2.2.2 (fun h => huw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.1 hnot (hg' 3).1 (fun h => hvu 3 0 h.1) (fun h => hvv (i := 1) (j := 3) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 3).2.1 (fun h => huu (i := 0) (j := 3) (by decide) h.1.symm) (fun h => hvu 1 3 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 3).2.2.1 (fun h => huu (i := 0) (j := 3) (by decide) h.1.symm) (fun h => hvu 1 3 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 3).2.2.2 (fun h => huw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.1 hnot (hg' 4).1 (fun h => hvu 4 0 h.1) (fun h => hvv (i := 1) (j := 4) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 4).2.1 (fun h => huu (i := 0) (j := 4) (by decide) h.1.symm) (fun h => hvu 1 4 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 4).2.2.1 (fun h => huu (i := 0) (j := 4) (by decide) h.1.symm) (fun h => hvu 1 4 h.1.symm),
        edge_other hH_adj (hg' 0).2.1 hnot (hg' 4).2.2.2 (fun h => huw 0 h.1.symm) (fun h => hvw 1 h.1.symm)⟩
  have hsum_le :
      (G.neighborSet (v' 0)).ncard + (G.neighborSet (v' 1)).ncard + (G.neighborSet (v' 2)).ncard +
      (G.neighborSet (v' 3)).ncard + (G.neighborSet (v' 4)).ncard +
      (G.neighborSet (u' 0)).ncard + (G.neighborSet (u' 1)).ncard + (G.neighborSet (u' 2)).ncard +
      (G.neighborSet w').ncard ≤ 3 * Fintype.card V := by
    rw [← sum_decide_toNat G (v' 0), ← sum_decide_toNat G (v' 1), ← sum_decide_toNat G (v' 2),
        ← sum_decide_toNat G (v' 3), ← sum_decide_toNat G (v' 4),
        ← sum_decide_toNat G (u' 0), ← sum_decide_toNat G (u' 1), ← sum_decide_toNat G (u' 2),
        ← sum_decide_toNat G w']
    simp only [← Finset.sum_add_distrib]
    calc _ ≤ ∑ _z : V, (3 : ℕ) := Finset.sum_le_sum fun z _ => by
          have p := grotzsch_sub_profile hGH hHcf v' u' w' hg' z
          have p0 := p 0; have p1 := p 1; have p2 := p 2; have p3 := p 3; have p4 := p 4
          simp only [Fin.reduceAdd] at p0 p1 p2 p3 p4
          exact dual_u0v1
            (decide (G.Adj z (v' 0))) (decide (G.Adj z (v' 1))) (decide (G.Adj z (v' 2)))
            (decide (G.Adj z (v' 3))) (decide (G.Adj z (v' 4)))
            (decide (G.Adj z (u' 0))) (decide (G.Adj z (u' 1))) (decide (G.Adj z (u' 2)))
            (decide (G.Adj z (u' 3))) (decide (G.Adj z (u' 4))) (decide (G.Adj z w'))
            p0.1 p1.1 p2.1 p3.1 p4.1
            p0.2.1 p0.2.2.1 p0.2.2.2 p1.2.1 p1.2.2.1 p1.2.2.2
            p2.2.1 p2.2.2.1 p2.2.2.2 p3.2.1 p3.2.2.1 p3.2.2.2
            p4.2.1 p4.2.2.1 p4.2.2.2
            (fun ⟨a, b, c⟩ => hno0 z ⟨of_decide_eq_true a, of_decide_eq_true b, of_decide_eq_true c⟩)
            (fun ⟨a, b, c, d⟩ => hno1 z ⟨of_decide_eq_true a, of_decide_eq_true b, of_decide_eq_true c, of_decide_eq_true d⟩)
      _ = 3 * Fintype.card V := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  exact nine_lt_contra (hmin (v' 0)) (hmin (v' 1)) (hmin (v' 2)) (hmin (v' 3)) (hmin (v' 4))
    (hmin (u' 0)) (hmin (u' 1)) (hmin (u' 2)) (hmin w') hsum_le

private lemma orbit_wu_contra {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ z : V, Fintype.card V < 3 * (G.neighborSet z).ncard)
    (hnoG : ¬ HasGrotzsch G)
    {x y : V} (hGH : G ≤ H) (hHcf : H.CliqueFree 3)
    (hH_adj : ∀ a b : V, H.Adj a b ↔ G.Adj a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (v' u' : Fin 5 → V) (w' : V)
    (hg' : ∀ i : Fin 5, H.Adj (v' i) (v' (i + 1)) ∧ H.Adj (u' i) (v' (i + 1)) ∧
      H.Adj (u' i) (v' (i + 4)) ∧ H.Adj w' (u' i))
    (hnot : ¬ G.Adj w' (u' 0)) : False := by
  have hvu := grotzsch_v_ne_u hHcf hg'
  have hvw := grotzsch_v_ne_w hHcf hg'
  have huu : ∀ {i j : Fin 5}, i ≠ j → u' i ≠ u' j := fun hij => grotzsch_u_ne_u hHcf hg' hij
  have huw := grotzsch_u_ne_w hg'
  have hnow : ∀ z : V, ¬ (G.Adj z (u' 0) ∧ G.Adj z (u' 1) ∧ G.Adj z (u' 2) ∧ G.Adj z (u' 3) ∧ G.Adj z (u' 4)) := by
    rintro z ⟨hz0, hz1, hz2, hz3, hz4⟩
    apply hnoG
    refine ⟨v', u', z, fun i => ⟨
      edge_other hH_adj (hg' 0).2.2.2 hnot (hg' i).1 (fun h => hvw i h.1) (fun h => hvu i 0 h.1),
      edge_other hH_adj (hg' 0).2.2.2 hnot (hg' i).2.1 (fun h => huw i h.1) (fun h => hvw (i + 1) h.2),
      edge_other hH_adj (hg' 0).2.2.2 hnot (hg' i).2.2.1 (fun h => huw i h.1) (fun h => hvw (i + 4) h.2),
      ?_⟩⟩
    fin_cases i
    · exact hz0
    · exact hz1
    · exact hz2
    · exact hz3
    · exact hz4
  have hno0 : ∀ z : V, ¬ (G.Adj z (v' 1) ∧ G.Adj z (v' 4) ∧ G.Adj z w') := by
    rintro z ⟨hz1, hz4, hzw⟩
    apply hnoG
    refine ⟨v', fun i => if i = 0 then z else u' i, w', fun i => ?_⟩
    fin_cases i
    · exact ⟨edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 0).1 (fun h => hvw 0 h.1) (fun h => hvu 0 0 h.1),
        hz1, hz4, hzw.symm⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 1).1 (fun h => hvw 1 h.1) (fun h => hvu 1 0 h.1),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 1).2.1 (fun h => huw 1 h.1) (fun h => huu (i := 0) (j := 1) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 1).2.2.1 (fun h => huw 1 h.1) (fun h => huu (i := 0) (j := 1) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 1).2.2.2 (fun h => huu (i := 0) (j := 1) (by decide) h.2.symm) (fun h => huw 0 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 2).1 (fun h => hvw 2 h.1) (fun h => hvu 2 0 h.1),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 2).2.1 (fun h => huw 2 h.1) (fun h => huu (i := 0) (j := 2) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 2).2.2.1 (fun h => huw 2 h.1) (fun h => huu (i := 0) (j := 2) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 2).2.2.2 (fun h => huu (i := 0) (j := 2) (by decide) h.2.symm) (fun h => huw 0 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 3).1 (fun h => hvw 3 h.1) (fun h => hvu 3 0 h.1),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 3).2.1 (fun h => huw 3 h.1) (fun h => huu (i := 0) (j := 3) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 3).2.2.1 (fun h => huw 3 h.1) (fun h => huu (i := 0) (j := 3) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 3).2.2.2 (fun h => huu (i := 0) (j := 3) (by decide) h.2.symm) (fun h => huw 0 h.1.symm)⟩
    · exact ⟨edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 4).1 (fun h => hvw 4 h.1) (fun h => hvu 4 0 h.1),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 4).2.1 (fun h => huw 4 h.1) (fun h => huu (i := 0) (j := 4) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 4).2.2.1 (fun h => huw 4 h.1) (fun h => huu (i := 0) (j := 4) (by decide) h.1.symm),
        edge_other hH_adj (hg' 0).2.2.2 hnot (hg' 4).2.2.2 (fun h => huu (i := 0) (j := 4) (by decide) h.2.symm) (fun h => huw 0 h.1.symm)⟩
  have hsum_le :
      (G.neighborSet (v' 0)).ncard + (G.neighborSet (v' 1)).ncard + (G.neighborSet (v' 2)).ncard +
      (G.neighborSet (v' 3)).ncard + (G.neighborSet (v' 4)).ncard +
      (G.neighborSet (u' 0)).ncard + (G.neighborSet (u' 1)).ncard + (G.neighborSet (u' 2)).ncard +
      (G.neighborSet (u' 3)).ncard + (G.neighborSet (u' 4)).ncard +
      2 * (G.neighborSet w').ncard ≤ 4 * Fintype.card V := by
    rw [← sum_decide_toNat G (v' 0), ← sum_decide_toNat G (v' 1), ← sum_decide_toNat G (v' 2),
        ← sum_decide_toNat G (v' 3), ← sum_decide_toNat G (v' 4),
        ← sum_decide_toNat G (u' 0), ← sum_decide_toNat G (u' 1), ← sum_decide_toNat G (u' 2),
        ← sum_decide_toNat G (u' 3), ← sum_decide_toNat G (u' 4), ← sum_decide_toNat G w',
        Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    calc _ ≤ ∑ _z : V, (4 : ℕ) := Finset.sum_le_sum fun z _ => by
          have p := grotzsch_sub_profile hGH hHcf v' u' w' hg' z
          have p0 := p 0; have p1 := p 1; have p2 := p 2; have p3 := p 3; have p4 := p 4
          simp only [Fin.reduceAdd] at p0 p1 p2 p3 p4
          exact dual_wu0
            (decide (G.Adj z (v' 0))) (decide (G.Adj z (v' 1))) (decide (G.Adj z (v' 2)))
            (decide (G.Adj z (v' 3))) (decide (G.Adj z (v' 4)))
            (decide (G.Adj z (u' 0))) (decide (G.Adj z (u' 1))) (decide (G.Adj z (u' 2)))
            (decide (G.Adj z (u' 3))) (decide (G.Adj z (u' 4))) (decide (G.Adj z w'))
            p0.1 p1.1 p2.1 p3.1 p4.1
            p0.2.1 p0.2.2.1 p0.2.2.2 p1.2.1 p1.2.2.1 p1.2.2.2
            p2.2.1 p2.2.2.1 p2.2.2.2 p3.2.1 p3.2.2.1 p3.2.2.2
            p4.2.1 p4.2.2.1 p4.2.2.2
            (fun ⟨a, b, c, d, e⟩ => hnow z ⟨of_decide_eq_true a, of_decide_eq_true b, of_decide_eq_true c, of_decide_eq_true d, of_decide_eq_true e⟩)
            (fun ⟨a, b, c⟩ => hno0 z ⟨of_decide_eq_true a, of_decide_eq_true b, of_decide_eq_true c⟩)
      _ = 4 * Fintype.card V := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  exact twelve_lt_contra (hmin (v' 0)) (hmin (v' 1)) (hmin (v' 2)) (hmin (v' 3)) (hmin (v' 4))
    (hmin (u' 0)) (hmin (u' 1)) (hmin (u' 2)) (hmin (u' 3)) (hmin (u' 4)) (hmin w') hsum_le

private lemma grotzsch_edge_step {V : Type} [Fintype V] (G : SimpleGraph V)
    (hmin : ∀ z : V, Fintype.card V < 3 * (G.neighborSet z).ncard)
    {x y : V}
    (H : SimpleGraph V) (hGH : G ≤ H) (hHcf : H.CliqueFree 3)
    (hH_adj : ∀ a b : V, H.Adj a b ↔ G.Adj a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (hHG : HasGrotzsch H) :
    HasGrotzsch G := by
  classical
  by_contra hnoG
  obtain ⟨v, u, w, hg⟩ := hHG
  by_cases hall : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)) ∧ G.Adj (u i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 4)) ∧ G.Adj w (u i)
  · exact hnoG ⟨v, u, w, hall⟩
  · push Not at hall
    obtain ⟨r, hr⟩ := hall
    by_cases h1 : G.Adj (v r) (v (r + 1))
    · by_cases h2 : G.Adj (u r) (v (r + 1))
      · by_cases h3 : G.Adj (u r) (v (r + 4))
        · have h4 : ¬ G.Adj w (u r) := hr h1 h2 h3
          exact orbit_wu_contra G H hmin hnoG hGH hHcf hH_adj
            (fun i => v (i + r)) (fun i => u (i + r)) w (grotzsch_rot hg r)
            (by simpa only [zero_add] using h4)
        · have hrot := grotzsch_rot hg r
          have hrev := grotzsch_rev hrot
          refine orbit_uv_contra G H hmin hnoG hGH hHcf hH_adj
            (fun i => v (-i + r)) (fun i => u (-i + r)) w hrev ?_
          have hneg0 : -(0 : Fin 5) + r = r := by fin_cases r <;> decide
          have hneg1 : -(1 : Fin 5) + r = r + 4 := by fin_cases r <;> decide
          rw [hneg0, hneg1]
          exact h3
      · refine orbit_uv_contra G H hmin hnoG hGH hHcf hH_adj
          (fun i => v (i + r)) (fun i => u (i + r)) w (grotzsch_rot hg r) ?_
        have h0r : (0 : Fin 5) + r = r := zero_add r
        have h1r : (1 : Fin 5) + r = r + 1 := add_comm 1 r
        rw [h0r, h1r]
        exact h2
    · refine orbit_vv_contra G H hmin hnoG hGH hHcf hH_adj
        (fun i => v (i + r)) (fun i => u (i + r)) w (grotzsch_rot hg r) ?_
      have h0r : (0 : Fin 5) + r = r := zero_add r
      have h1r : (1 : Fin 5) + r = r + 1 := add_comm 1 r
      rw [h0r, h1r]
      exact h1

private lemma exists_maximal_no_grotzsch {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hmin : ∀ z : V, Fintype.card V < 3 * (G.neighborSet z).ncard)
    (hnoG : ¬ HasGrotzsch G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧ ¬ HasGrotzsch H ∧
      ∀ u v : V, u ≠ v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w := by
  classical
  suffices h : ∀ m : ℕ, ∀ G : SimpleGraph V, G.CliqueFree 3 →
      (∀ z : V, Fintype.card V < 3 * (G.neighborSet z).ncard) →
      ¬ HasGrotzsch G →
      Fintype.card (Sym2 V) - G.edgeSet.ncard ≤ m →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧ ¬ HasGrotzsch H ∧
        ∀ u v : V, u ≠ v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w from
    h (Fintype.card (Sym2 V) - G.edgeSet.ncard) G hTF hmin hnoG (le_refl _)
  intro m
  induction m with
  | zero =>
    intro G hTF _ hnoG hm
    refine ⟨G, le_refl _, hTF, hnoG, ?_⟩
    intro u v huv hna
    exfalso
    have hcard : G.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by
      rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
      exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    have heq : G.edgeSet = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ, Nat.card_eq_fintype_card]; omega) (Set.toFinite _)
    have hmem : s(u, v) ∈ G.edgeSet := by rw [heq]; trivial
    exact hna hmem
  | succ m ih =>
    intro G hTF hmin hnoG hm
    by_cases hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w
    · exact ⟨G, le_refl _, hTF, hnoG, hmax⟩
    · push Not at hmax
      obtain ⟨u, v, huv, hna, hno_cn⟩ := hmax
      let G' : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
      have hGG' : G ≤ G' := le_sup_left
      have hG'_adj : ∀ a b : V, G'.Adj a b ↔ G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
        intro a b
        simp only [G', SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
        constructor
        · rintro (h | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
          · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩
      have hG'_TF : G'.CliqueFree 3 := by
        intro s hs
        obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
        have h1 : G'.Adj a b := hs.1 (by simp) (by simp) hab
        have h2 : G'.Adj b c := hs.1 (by simp) (by simp) hbc
        have h3 : G'.Adj a c := hs.1 (by simp) (by simp) hac
        rw [hG'_adj] at h1 h2 h3
        by_cases g1 : G.Adj a b
        · by_cases g2 : G.Adj b c
          · by_cases g3 : G.Adj a c
            · exact not_adj_of_cliqueFree_three hTF g1 g2 g3
            · rcases h3 with h3 | ⟨ha, hc⟩ | ⟨ha, hc⟩
              · exact g3 h3
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g1 g2.symm
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g2.symm g1
          · rcases h2 with h2 | ⟨hb, hc⟩ | ⟨hb, hc⟩
            · exact g2 h2
            · rcases h3 with g3 | ⟨ha, _⟩ | ⟨_, hcu⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g1.symm g3.symm
              · exact hab (ha.trans hb.symm)
              · exact huv (hcu.symm.trans hc)
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨ha, _⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g3.symm g1.symm
              · exact huv (hc.symm.trans hcv)
              · exact hab (ha.trans hb.symm)
        · rcases h1 with h1 | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact g1 h1
          · rcases h2 with g2 | ⟨hbu, _⟩ | ⟨_, hcu⟩
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨hau, _⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g3 g2
              · exact hbc (hb.trans hcv.symm)
              · exact huv (ha.symm.trans hau)
            · exact huv (hb.symm.trans hbu).symm
            · exact hac (ha.trans hcu.symm)
          · rcases h2 with g2 | ⟨_, hcv⟩ | ⟨hbv, _⟩
            · rcases h3 with g3 | ⟨hau, _⟩ | ⟨_, hcu⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g2 g3
              · exact huv (hau.symm.trans ha)
              · exact hbc (hb.trans hcu.symm)
            · exact hac (ha.trans hcv.symm)
            · exact huv (hb.symm.trans hbv)
      have hG'_min : ∀ z : V, Fintype.card V < 3 * (G'.neighborSet z).ncard := fun z => by
        have hsub : G.neighborSet z ⊆ G'.neighborSet z := fun w hw => hGG' hw
        have hcard : (G.neighborSet z).ncard ≤ (G'.neighborSet z).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
        have := hmin z
        omega
      have hG'_noG : ¬ HasGrotzsch G' := fun hG' =>
        hnoG (grotzsch_edge_step G hmin G' hGG' hG'_TF hG'_adj hG')
      have hstrict : G.edgeSet.ncard < G'.edgeSet.ncard := by
        apply Set.ncard_lt_ncard _ (Set.toFinite _)
        rw [Set.ssubset_iff_subset_ne]
        refine ⟨SimpleGraph.edgeSet_mono hGG', fun heq => ?_⟩
        have hmem : s(u, v) ∈ G'.edgeSet :=
          (hG'_adj u v).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        rw [← heq] at hmem
        exact hna hmem
      have hcard_G' : G'.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by
        rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
        exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      have hstep_m : Fintype.card (Sym2 V) - G'.edgeSet.ncard ≤ m := by omega
      obtain ⟨H, hG'H, hHTF, hHnoG, hHmax⟩ := ih G' hG'_TF hG'_min hG'_noG hstep_m
      exact ⟨H, hGG'.trans hG'H, hHTF, hHnoG, hHmax⟩

end OMA.E128Brandt

theorem OMA.solution : OMA.R_Erdos128_erdos_128_R2_H2_R1.H1 := by
  intro V _ G hcf hcol3 hmin _
  classical
  by_contra hnoG
  obtain ⟨H, hGH, hHcf, hHnoG, hHmax⟩ :=
    OMA.E128Brandt.exists_maximal_no_grotzsch G hcf hmin hnoG
  have hHcol3 : ¬ H.Colorable 3 := fun ⟨c⟩ =>
    hcol3 ⟨SimpleGraph.Coloring.mk c fun h => c.valid (hGH h)⟩
  have hHmin : ∀ v : V, Fintype.card V < 3 * (H.neighborSet v).ncard := fun v => by
    have hsub : G.neighborSet v ⊆ H.neighborSet v := fun w hw => hGH hw
    have hcard : (G.neighborSet v).ncard ≤ (H.neighborSet v).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have := hmin v
    omega
  have hne : Nonempty V := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    exact hHcol3 ⟨SimpleGraph.Coloring.mk (fun x => (hE.false x).elim)
      (fun {a _} _ => (hE.false a).elim)⟩
  obtain ⟨u₀⟩ := hne
  have hHedge : ∃ u v : V, H.Adj u v := by
    have hpos : 0 < (H.neighborSet u₀).ncard := by have := hHmin u₀; omega
    obtain ⟨v₀, hv₀⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (H.neighborSet u₀).ncard ≠ 0)
    exact ⟨u₀, v₀, hv₀⟩
  have hC6 : ∃ a1 a2 a3 b1 b2 b3 : V,
      H.Adj a1 b2 ∧ H.Adj a1 b3 ∧ H.Adj a2 b1 ∧ H.Adj a2 b3 ∧ H.Adj a3 b1 ∧ H.Adj a3 b2 ∧
      ¬ H.Adj a1 b1 ∧ ¬ H.Adj a2 b2 ∧ ¬ H.Adj a3 b3 := by
    by_contra hno
    apply hHcol3
    apply OMA.E128Brandt.LPR.prop_3_7_colorable3 H hHcf hHmax hHedge
    intro a1 a2 a3 b1 b2 b3 e12 e13 e21 e23 e31 e32 n1 n2
    by_contra n3
    exact hno ⟨a1, a2, a3, b1, b2, b3, e12, e13, e21, e23, e31, e32, n1, n2, n3⟩
  obtain ⟨a1, a2, a3, b1, b2, b3, e12, e13, e21, e23, e31, e32, n1, n2, n3⟩ := hC6
  exact hHnoG (OMA.E128Brandt.LPR.lemma_3_1 H hHcf hHmax hHmin
    a1 a2 a3 b1 b2 b3 e12 e13 e21 e23 e31 e32 n1 n2 n3)
