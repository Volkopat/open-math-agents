import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H1_R1
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Reduction `Erdos713.erdos_713.parts.i.R1.H1.R1.H2.R1` — Girth-4/6/8 decomposition with affine-plane and Wenger `W_3(p)` lower bounds

Decomposes `Erdos713.erdos_713.parts.i.R1.H1.R1.H2` (connected bipartite cores `J` on `Fin r` with
minimum degree at least `2`, not isomorphic to `C_4`, and superlinear Turán number) into three
disjoint girth regimes, proving unconditionally inside this file:

1. **Affine-plane `C_4` lower bound (`cycle_four_extremal_subseq`)**: For every prime `p`, the
   bipartite affine incidence graph on `(ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)` is `K_{2,2}`-free
   and has at least `p^3` edges, proving `p^3 ≤ extremalNumber (2 * p^2) (K_{2,2})`.
2. **Wenger `W_3(p)` `C_6` lower bound (`cycle_six_extremal_subseq`)**: For every prime `p`,
   Wenger's bipartite graph `W_3(p)` on `(ZMod p)^3 ⊕ (ZMod p)^3` (`a_2 + b_2 = a_1 b_1`,
   `a_3 + b_3 = a_1^2 b_1`) is `cycleGraph 6`-free (proved directly over the field `ZMod p` via
   elimination of `u_i - u_3`) and has at least `p^4` edges, proving
   `p^4 ≤ extremalNumber (2 * p^3) (cycleGraph 6)`.
3. **Structural order and edge bounds**:
   - If `K_{2,2} ⊑ J` and `J ≄ K_{2,2}`, then `5 ≤ r` and `6 ≤ J.edgeFinset.card`.
   - If `¬ K_{2,2} ⊑ J`, then `6 ≤ r` and `6 ≤ J.edgeFinset.card`.
   - If `¬ K_{2,2} ⊑ J` and `¬ cycleGraph 6 ⊑ J`, then `8 ≤ r` and `8 ≤ J.edgeFinset.card`.

Splits into:
* `H1`: Girth 4 (`K_{2,2} ⊑ J`, `5 ≤ r`, `6 ≤ |E(J)|`, with `p^3 ≤ ex(2 * p^2, J)` for all primes `p`).
* `H2`: Girth 6 (`¬ K_{2,2} ⊑ J`, `cycleGraph 6 ⊑ J`, `6 ≤ r`, `6 ≤ |E(J)|`, with `p^4 ≤ ex(2 * p^3, J)` for all primes `p`).
* `H3`: Girth at least 8 (`¬ K_{2,2} ⊑ J`, `¬ cycleGraph 6 ⊑ J`, `8 ≤ r`, `8 ≤ |E(J)|`).

Reference: R. Wenger, Extremal graphs with no C^4s, C^6s, or C^10s, J. Combin. Theory Ser. B 52 (1991), 113-116.
-/

-- Credit: @sanchan (extending OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1 by @zarnab222-dev)

namespace OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1

open SimpleGraph Filter Asymptotics Finset
open scoped Classical BigOperators

-- ### Part 1: Affine-plane C4-free lower bound

theorem affine_common_unique {K : Type*} [Field K] {a b u v : K × K}
    (hab : a ≠ b)
    (hau : a.2 + u.2 = a.1 * u.1) (hbu : b.2 + u.2 = b.1 * u.1)
    (hav : a.2 + v.2 = a.1 * v.1) (hbv : b.2 + v.2 = b.1 * v.1) : u = v := by
  have hx : a.1 ≠ b.1 := by
    intro h1
    apply hab
    apply Prod.ext h1
    have h2 : a.2 + u.2 = b.2 + u.2 := by rw [hau, hbu, h1]
    exact add_right_cancel h2
  have hprod : (a.1 - b.1) * (u.1 - v.1) = 0 := by
    linear_combination -hau + hbu + hav - hbv
  have hu1 : u.1 = v.1 := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hx))
  apply Prod.ext hu1
  have hu2 : a.2 + u.2 = a.2 + v.2 := by rw [hau, hav, hu1]
  exact add_left_cancel hu2

theorem cycle_four_extremal_subseq {p : ℕ} (hp : p.Prime) :
    p ^ 3 ≤ extremalNumber (2 * p ^ 2) (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let X : SimpleGraph ((ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)) := {
    Adj := fun a b => match a, b with
      | .inl x, .inr y | .inr x, .inl y => x.2 + y.2 = x.1 * y.1
      | _, _ => False
    symm := by
      refine ⟨?_⟩
      rintro (x | x) (y | y) h
      all_goals first | exact h | (dsimp only at h ⊢; linear_combination h)
    loopless := by
      refine ⟨?_⟩
      rintro (x | x) h <;> exact h }
  have hfree : (completeBipartiteGraph (Fin 2) (Fin 2)).Free X := by
    have hcommon : ∀ a b u v, a ≠ b →
        X.Adj a u → X.Adj b u → X.Adj a v → X.Adj b v → u = v := by
      rintro (a | a) (b | b) (u | u) (v | v) hab hau hbu hav hbv
      all_goals simp only [X, ne_eq, Sum.inl.injEq, Sum.inr.injEq, not_false_eq_true,
        Sum.inl_ne_inr, Sum.inr_ne_inl] at hab hau hbu hav hbv ⊢
      · exact affine_common_unique hab hau hbu hav hbv
      · exact affine_common_unique hab hau hbu hav hbv
    intro h
    let f := h.some
    have hadj (i j : Fin 2) : X.Adj (f (.inl i)) (f (.inr j)) :=
      f.toHom.map_rel' (Or.inl ⟨rfl, rfl⟩)
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hne : f (.inl 0) ≠ f (.inl 1) := fun h => h01 (Sum.inl.inj (f.injective h))
    have heq := hcommon _ _ _ _ hne (hadj 0 0) (hadj 1 0) (hadj 0 1) (hadj 1 1)
    exact h01 (Sum.inr.inj (f.injective heq))
  have hedges : p ^ 3 ≤ X.edgeFinset.card := by
    let fn : (ZMod p × ZMod p) × ZMod p → X.edgeFinset := fun z =>
      ⟨s(Sum.inl z.1, Sum.inr (z.2, z.1.1 * z.2 - z.1.2)), by
        rw [mem_edgeFinset]
        show z.1.2 + (z.1.1 * z.2 - z.1.2) = z.1.1 * z.2
        ring⟩
    have hinj : Function.Injective fn := by
      intro a b h
      have he := Sym2.eq_iff.mp (congrArg Subtype.val h)
      rcases he with ⟨hl, hr⟩ | ⟨hl, _⟩
      · exact Prod.ext (Sum.inl.inj hl) (congrArg Prod.fst (Sum.inr.inj hr))
      · exact (Sum.inl_ne_inr hl).elim
    have hle := Fintype.card_le_of_injective fn hinj
    simpa only [Fintype.card_coe, Fintype.card_prod, ZMod.card, pow_succ, pow_zero, one_mul] using hle
  have hbound := hedges.trans (card_edgeFinset_le_extremalNumber hfree)
  simpa [Fintype.card_sum, Fintype.card_prod, ZMod.card, two_mul, pow_two] using hbound

-- ### Part 2: Wenger graph W_3(p) and C_6 lower bound

theorem wenger_no_six_cycle {K : Type*} [Field K]
    {a1 a2 a3 b1 b2 b3 : K × K × K}
    (ha12 : a1 ≠ a2) (ha23 : a2 ≠ a3) (ha31 : a3 ≠ a1) (hb12 : b1 ≠ b2)
    (e11 : a1.2.1 + b1.2.1 = a1.1 * b1.1 ∧ a1.2.2 + b1.2.2 = a1.1 ^ 2 * b1.1)
    (e21 : a2.2.1 + b1.2.1 = a2.1 * b1.1 ∧ a2.2.2 + b1.2.2 = a2.1 ^ 2 * b1.1)
    (e22 : a2.2.1 + b2.2.1 = a2.1 * b2.1 ∧ a2.2.2 + b2.2.2 = a2.1 ^ 2 * b2.1)
    (e32 : a3.2.1 + b2.2.1 = a3.1 * b2.1 ∧ a3.2.2 + b2.2.2 = a3.1 ^ 2 * b2.1)
    (e33 : a3.2.1 + b3.2.1 = a3.1 * b3.1 ∧ a3.2.2 + b3.2.2 = a3.1 ^ 2 * b3.1)
    (e13 : a1.2.1 + b3.2.1 = a1.1 * b3.1 ∧ a1.2.2 + b3.2.2 = a1.1 ^ 2 * b3.1) : False := by
  have hx12 : a1.1 ≠ a2.1 := by
    intro h
    apply ha12
    refine Prod.ext h (Prod.ext ?_ ?_)
    · linear_combination e11.1 - e21.1 + b1.1 * h
    · linear_combination e11.2 - e21.2 + b1.1 * (a1.1 + a2.1) * h
  have hx23 : a2.1 ≠ a3.1 := by
    intro h
    apply ha23
    refine Prod.ext h (Prod.ext ?_ ?_)
    · linear_combination e22.1 - e32.1 + b2.1 * h
    · linear_combination e22.2 - e32.2 + b2.1 * (a2.1 + a3.1) * h
  have hx31 : a3.1 ≠ a1.1 := by
    intro h
    apply ha31
    refine Prod.ext h (Prod.ext ?_ ?_)
    · linear_combination e33.1 - e13.1 + b3.1 * h
    · linear_combination e33.2 - e13.2 + b3.1 * (a3.1 + a1.1) * h
  have hL1 : (a1.1 - a2.1) * (b1.1 - b3.1) + (a2.1 - a3.1) * (b2.1 - b3.1) = 0 := by
    linear_combination -e11.1 + e21.1 - e22.1 + e32.1 - e33.1 + e13.1
  have hL2 : (a1.1 ^ 2 - a2.1 ^ 2) * (b1.1 - b3.1) + (a2.1 ^ 2 - a3.1 ^ 2) * (b2.1 - b3.1) = 0 := by
    linear_combination -e11.2 + e21.2 - e22.2 + e32.2 - e33.2 + e13.2
  have hprod : (a2.1 - a3.1) * (a3.1 - a1.1) * (b2.1 - b3.1) = 0 := by
    linear_combination -(a1.1 + a2.1) * hL1 + hL2
  have hnz1 : (a2.1 - a3.1) * (a3.1 - a1.1) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hx23) (sub_ne_zero.mpr hx31)
  have hb23 : b2.1 - b3.1 = 0 := (mul_eq_zero.mp hprod).resolve_left hnz1
  have hb13_prod : (a1.1 - a2.1) * (b1.1 - b3.1) = 0 := by
    linear_combination hL1 - (a2.1 - a3.1) * hb23
  have hb13 : b1.1 - b3.1 = 0 := (mul_eq_zero.mp hb13_prod).resolve_left (sub_ne_zero.mpr hx12)
  have hu : b1.1 = b2.1 := by linear_combination hb13 - hb23
  apply hb12
  refine Prod.ext hu (Prod.ext ?_ ?_)
  · linear_combination e21.1 - e22.1 + a2.1 * hu
  · linear_combination e21.2 - e22.2 + a2.1 ^ 2 * hu

theorem cycle_six_extremal_subseq {p : ℕ} (hp : p.Prime) :
    p ^ 4 ≤ extremalNumber (2 * p ^ 3) (cycleGraph 6) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let W : SimpleGraph ((ZMod p × ZMod p × ZMod p) ⊕ (ZMod p × ZMod p × ZMod p)) := {
    Adj := fun u v => match u, v with
      | .inl a, .inr b => a.2.1 + b.2.1 = a.1 * b.1 ∧ a.2.2 + b.2.2 = a.1 ^ 2 * b.1
      | .inr b, .inl a => a.2.1 + b.2.1 = a.1 * b.1 ∧ a.2.2 + b.2.2 = a.1 ^ 2 * b.1
      | _, _ => False
    symm := by
      refine ⟨?_⟩
      rintro (a | b) (c | d) h <;> exact h
    loopless := by
      refine ⟨?_⟩
      rintro (a | b) h <;> exact h }
  have hfree : (cycleGraph 6).Free W := by
    intro h
    let f := h.some
    have h01 : W.Adj (f 0) (f 1) := f.toHom.map_rel' (by decide : (cycleGraph 6).Adj 0 1)
    have h12 : W.Adj (f 1) (f 2) := f.toHom.map_rel' (by decide : (cycleGraph 6).Adj 1 2)
    have h23 : W.Adj (f 2) (f 3) := f.toHom.map_rel' (by decide : (cycleGraph 6).Adj 2 3)
    have h34 : W.Adj (f 3) (f 4) := f.toHom.map_rel' (by decide : (cycleGraph 6).Adj 3 4)
    have h45 : W.Adj (f 4) (f 5) := f.toHom.map_rel' (by decide : (cycleGraph 6).Adj 4 5)
    have h50 : W.Adj (f 5) (f 0) := f.toHom.map_rel' (by decide : (cycleGraph 6).Adj 5 0)
    have hne : ∀ i j : Fin 6, i ≠ j → f i ≠ f j := fun i j hij => f.injective.ne hij
    cases hf0 : f 0 with
    | inl a1 =>
      rw [hf0] at h01 h50
      cases hf1 : f 1 with
      | inl _ => rw [hf1] at h01; exact h01
      | inr b1 =>
        rw [hf1] at h01 h12
        cases hf2 : f 2 with
        | inr _ => rw [hf2] at h12; exact h12
        | inl a2 =>
          rw [hf2] at h12 h23
          cases hf3 : f 3 with
          | inl _ => rw [hf3] at h23; exact h23
          | inr b2 =>
            rw [hf3] at h23 h34
            cases hf4 : f 4 with
            | inr _ => rw [hf4] at h34; exact h34
            | inl a3 =>
              rw [hf4] at h34 h45
              cases hf5 : f 5 with
              | inl _ => rw [hf5] at h45; exact h45
              | inr b3 =>
                rw [hf5] at h45 h50
                exact wenger_no_six_cycle
                  (fun e => hne 0 2 (by decide) (by rw [hf0, hf2, e]))
                  (fun e => hne 2 4 (by decide) (by rw [hf2, hf4, e]))
                  (fun e => hne 4 0 (by decide) (by rw [hf4, hf0, e]))
                  (fun e => hne 1 3 (by decide) (by rw [hf1, hf3, e]))
                  h01 h12 h23 h34 h45 h50
    | inr b3 =>
      rw [hf0] at h01 h50
      cases hf1 : f 1 with
      | inr _ => rw [hf1] at h01; exact h01
      | inl a1 =>
        rw [hf1] at h01 h12
        cases hf2 : f 2 with
        | inl _ => rw [hf2] at h12; exact h12
        | inr b1 =>
          rw [hf2] at h12 h23
          cases hf3 : f 3 with
          | inr _ => rw [hf3] at h23; exact h23
          | inl a2 =>
            rw [hf3] at h23 h34
            cases hf4 : f 4 with
            | inl _ => rw [hf4] at h34; exact h34
            | inr b2 =>
              rw [hf4] at h34 h45
              cases hf5 : f 5 with
              | inr _ => rw [hf5] at h45; exact h45
              | inl a3 =>
                rw [hf5] at h45 h50
                exact wenger_no_six_cycle
                  (fun e => hne 1 3 (by decide) (by rw [hf1, hf3, e]))
                  (fun e => hne 3 5 (by decide) (by rw [hf3, hf5, e]))
                  (fun e => hne 5 1 (by decide) (by rw [hf5, hf1, e]))
                  (fun e => hne 2 4 (by decide) (by rw [hf2, hf4, e]))
                  h12 h23 h34 h45 h50 h01
  have hedges : p ^ 4 ≤ W.edgeFinset.card := by
    let fn : (ZMod p × ZMod p × ZMod p) × ZMod p → W.edgeFinset := fun z =>
      ⟨s(Sum.inl z.1, Sum.inr (z.2, z.1.1 * z.2 - z.1.2.1, z.1.1 ^ 2 * z.2 - z.1.2.2)), by
        rw [mem_edgeFinset]
        show z.1.2.1 + (z.1.1 * z.2 - z.1.2.1) = z.1.1 * z.2 ∧
          z.1.2.2 + (z.1.1 ^ 2 * z.2 - z.1.2.2) = z.1.1 ^ 2 * z.2
        constructor <;> ring⟩
    have hinj : Function.Injective fn := by
      intro a b h
      have he := Sym2.eq_iff.mp (congrArg Subtype.val h)
      rcases he with ⟨hl, hr⟩ | ⟨hl, _⟩
      · exact Prod.ext (Sum.inl.inj hl) (congrArg Prod.fst (Sum.inr.inj hr))
      · exact (Sum.inl_ne_inr hl).elim
    have hle := Fintype.card_le_of_injective fn hinj
    simpa only [Fintype.card_coe, Fintype.card_prod, ZMod.card, pow_succ, pow_zero, one_mul,
      mul_assoc] using hle
  have hbound := hedges.trans (card_edgeFinset_le_extremalNumber hfree)
  have hcard : Fintype.card ((ZMod p × ZMod p × ZMod p) ⊕ (ZMod p × ZMod p × ZMod p)) = 2 * p ^ 3 := by
    simp only [Fintype.card_sum, Fintype.card_prod, ZMod.card]
    ring
  rwa [hcard] at hbound

-- ### Part 3: Structural order and edge bounds for connected bipartite min-degree-2 cores

theorem fin2_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem fin2_eq_of_ne_ne {a b d : Fin 2} (ha : a ≠ d) (hb : b ≠ d) : a = b := by
  revert a b d
  decide

theorem card_le_edges_of_min_deg_two {r : ℕ} (J : SimpleGraph (Fin r))
    (hmin : ∀ v, 2 ≤ J.degree v) : r ≤ J.edgeFinset.card := by
  have hsum := J.sum_degrees_eq_twice_card_edges
  have hlb : 2 * r ≤ ∑ v : Fin r, J.degree v := by
    calc 2 * r = ∑ _v : Fin r, 2 := by simp [mul_comm]
      _ ≤ ∑ v : Fin r, J.degree v := Finset.sum_le_sum fun v _ => hmin v
  omega

theorem six_le_edges_of_five_le_bipartite {r : ℕ} (J : SimpleGraph (Fin r))
    (hbip : J.IsBipartite) (hmin : ∀ v, 2 ≤ J.degree v) (hr : 5 ≤ r) :
    6 ≤ J.edgeFinset.card := by
  by_cases hr6 : 6 ≤ r
  · exact hr6.trans (card_le_edges_of_min_deg_two J hmin)
  · have hr5 : r = 5 := by omega
    obtain ⟨c⟩ := hbip
    let A := Finset.univ.filter (fun v : Fin r => c v = 0)
    let B := Finset.univ.filter (fun v : Fin r => c v = 1)
    have hAB : A.card + B.card = r := by
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro v h1 h2
        have c1 := (Finset.mem_filter.mp h1).2
        have c2 := (Finset.mem_filter.mp h2).2
        rw [c1] at c2
        exact absurd c2 (by decide)
      have hunion : A ∪ B = Finset.univ := by
        ext v
        simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact fin2_eq_zero_or_one (c v)
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    have hside : ∀ S : Finset (Fin r), (∀ u ∈ S, ∀ v ∈ S, ¬ J.Adj u v) →
        ∑ v ∈ S, J.degree v ≤ J.edgeFinset.card := by
      intro S hind
      have hpw : (S : Set (Fin r)).PairwiseDisjoint (fun v => J.incidenceFinset v) := by
        intro u hu v hv huv
        change Disjoint (J.incidenceFinset u) (J.incidenceFinset v)
        rw [Finset.disjoint_left]
        intro e heu hev
        induction e using Sym2.ind with
        | h x y =>
          obtain ⟨hxy, hu'⟩ := (J.mem_incidenceFinset u s(x, y)).mp heu
          obtain ⟨_, hv'⟩ := (J.mem_incidenceFinset v s(x, y)).mp hev
          simp only [Sym2.mem_iff] at hu' hv'
          rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
          · exact huv rfl
          · exact hind _ hu _ hv hxy
          · exact hind _ hv _ hu hxy
          · exact huv rfl
      have hsub : S.biUnion (fun v => J.incidenceFinset v) ⊆ J.edgeFinset := by
        intro e he
        obtain ⟨v, _, hve⟩ := Finset.mem_biUnion.mp he
        exact J.incidenceFinset_subset v hve
      calc ∑ v ∈ S, J.degree v
          = ∑ v ∈ S, (J.incidenceFinset v).card := by simp [J.card_incidenceFinset_eq_degree]
        _ = (S.biUnion (fun v => J.incidenceFinset v)).card := (Finset.card_biUnion hpw).symm
        _ ≤ J.edgeFinset.card := Finset.card_le_card hsub
    have hAind : ∀ u ∈ A, ∀ v ∈ A, ¬ J.Adj u v := by
      intro u hu v hv hadj
      exact c.valid hadj ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
    have hBind : ∀ u ∈ B, ∀ v ∈ B, ¬ J.Adj u v := by
      intro u hu v hv hadj
      exact c.valid hadj ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
    rcases (by omega : 3 ≤ A.card ∨ 3 ≤ B.card) with hA3 | hB3
    · calc 6 ≤ 2 * A.card := by omega
        _ = ∑ _v ∈ A, 2 := by simp [mul_comm]
        _ ≤ ∑ v ∈ A, J.degree v := Finset.sum_le_sum fun v _ => hmin v
        _ ≤ J.edgeFinset.card := hside A hAind
    · calc 6 ≤ 2 * B.card := by omega
        _ = ∑ _v ∈ B, 2 := by simp [mul_comm]
        _ ≤ ∑ v ∈ B, J.degree v := Finset.sum_le_sum fun v _ => hmin v
        _ ≤ J.edgeFinset.card := hside B hBind

theorem five_le_card_of_c4_not_iso {r : ℕ} (J : SimpleGraph (Fin r))
    (hbip : J.IsBipartite) (hc4 : completeBipartiteGraph (Fin 2) (Fin 2) ⊑ J)
    (hnotiso : ¬ Nonempty (J ≃g completeBipartiteGraph (Fin 2) (Fin 2))) : 5 ≤ r := by
  obtain ⟨f⟩ := hc4
  have hge4 : 4 ≤ r := by
    have h := Fintype.card_le_of_injective f f.injective
    simpa [Fintype.card_sum] using h
  by_contra hlt5
  have hr4 : r = 4 := by omega
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by simp [Fintype.card_sum, hr4]⟩
  let e : (Fin 2 ⊕ Fin 2) ≃ Fin r := Equiv.ofBijective f hbij
  obtain ⟨c⟩ := hbip
  have hadj (i j : Fin 2) : J.Adj (e (.inl i)) (e (.inr j)) :=
    f.toHom.map_rel' (Or.inl ⟨rfl, rfl⟩)
  have hc_in : c (e (.inl 0)) = c (e (.inl 1)) :=
    fin2_eq_of_ne_ne (c.valid (hadj 0 0)) (c.valid (hadj 1 0))
  have hc_out : c (e (.inr 0)) = c (e (.inr 1)) :=
    fin2_eq_of_ne_ne (c.valid (hadj 0 0)).symm (c.valid (hadj 0 1)).symm
  have hmap : ∀ a b : Fin 2 ⊕ Fin 2, J.Adj (e a) (e b) ↔ (completeBipartiteGraph (Fin 2) (Fin 2)).Adj a b := by
    intro a b
    constructor
    · intro hab
      cases a with
      | inl i =>
        cases b with
        | inl j =>
          exfalso
          fin_cases i <;> fin_cases j
          · exact hab.ne rfl
          · exact c.valid hab hc_in
          · exact c.valid hab hc_in.symm
          · exact hab.ne rfl
        | inr j => exact Or.inl ⟨rfl, rfl⟩
      | inr i =>
        cases b with
        | inl j => exact Or.inr ⟨rfl, rfl⟩
        | inr j =>
          exfalso
          fin_cases i <;> fin_cases j
          · exact hab.ne rfl
          · exact c.valid hab hc_out
          · exact c.valid hab hc_out.symm
          · exact hab.ne rfl
    · intro hab
      exact f.toHom.map_rel' hab
  apply hnotiso
  refine ⟨⟨e.symm, ?_⟩⟩
  intro x y
  have hx := e.apply_symm_apply x
  have hy := e.apply_symm_apply y
  have := hmap (e.symm x) (e.symm y)
  rw [hx, hy] at this
  exact this.symm

theorem no_c4_pair {r : ℕ} (J : SimpleGraph (Fin r))
    (hfree : ¬ completeBipartiteGraph (Fin 2) (Fin 2) ⊑ J)
    {a b u v : Fin r} (hab : a ≠ b) (huv : u ≠ v)
    (hau : J.Adj a u) (hav : J.Adj a v) (hbu : J.Adj b u) (hbv : J.Adj b v) : False := by
  have hne : a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v :=
    ⟨hau.ne, hav.ne, hbu.ne, hbv.ne⟩
  let g : Fin 2 ⊕ Fin 2 → Fin r := fun z => match z with
    | .inl 0 => a | .inl 1 => b | .inr 0 => u | .inr 1 => v
  apply hfree
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · rintro (x | x) (y | y) h
    · simp [completeBipartiteGraph] at h
    · fin_cases x <;> fin_cases y <;> assumption
    · fin_cases x <;> fin_cases y <;> exact SimpleGraph.adj_symm J (by assumption)
    · simp [completeBipartiteGraph] at h
  · rintro (x | x) (y | y) h
    · fin_cases x <;> fin_cases y <;> simp_all [g]
    · fin_cases x <;> fin_cases y <;> simp_all [g]
    · fin_cases x <;> fin_cases y <;> simp_all [g, Ne.symm]
    · fin_cases x <;> fin_cases y <;> simp_all [g]

theorem no_c6_hex {r : ℕ} (J : SimpleGraph (Fin r))
    (hfree : ¬ cycleGraph 6 ⊑ J)
    {v0 v1 v2 v3 v4 v5 : Fin r}
    (h01 : J.Adj v0 v1) (h12 : J.Adj v1 v2) (h23 : J.Adj v2 v3)
    (h34 : J.Adj v3 v4) (h45 : J.Adj v4 v5) (h50 : J.Adj v5 v0)
    (hcard : ({v0, v1, v2, v3, v4, v5} : Finset (Fin r)).card = 6) : False := by
  let g : Fin 6 → Fin r := ![v0, v1, v2, v3, v4, v5]
  have himg : (Finset.univ : Finset (Fin 6)).image g = {v0, v1, v2, v3, v4, v5} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [g]
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
  have hinj : Function.Injective g := by
    have hcard_img : ((Finset.univ : Finset (Fin 6)).image g).card = (Finset.univ : Finset (Fin 6)).card := by
      rw [himg, hcard]; simp
    have hinjOn := (Finset.card_image_iff (f := g) (s := Finset.univ)).mp hcard_img
    intro a b hab
    exact hinjOn (Finset.mem_univ a) (Finset.mem_univ b) hab
  apply hfree
  refine ⟨⟨⟨g, ?_⟩, hinj⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [cycleGraph_adj] at hij
  all_goals first
    | (exfalso; revert hij; decide)
    | exact h01 | exact h01.symm
    | exact h12 | exact h12.symm
    | exact h23 | exact h23.symm
    | exact h34 | exact h34.symm
    | exact h45 | exact h45.symm
    | exact h50 | exact h50.symm

theorem exists_other_neighbor {r : ℕ} (J : SimpleGraph (Fin r))
    (hmin : ∀ v, 2 ≤ J.degree v) (v a : Fin r) : ∃ w, J.Adj v w ∧ w ≠ a := by
  have hlt : ({a} : Finset (Fin r)).card < (J.neighborFinset v).card := by
    rw [Finset.card_singleton, J.card_neighborFinset_eq_degree]
    have := hmin v
    omega
  obtain ⟨w, hwN, hwa⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨w, (J.mem_neighborFinset v w).mp hwN, by simpa using hwa⟩

theorem six_le_card_of_c4_free {r : ℕ} (J : SimpleGraph (Fin r))
    (hbip : J.IsBipartite) (hconn : J.Connected) (hmin : ∀ v, 2 ≤ J.degree v)
    (hc4 : ¬ completeBipartiteGraph (Fin 2) (Fin 2) ⊑ J) : 6 ≤ r := by
  obtain ⟨v0⟩ := hconn.nonempty
  obtain ⟨c⟩ := hbip
  obtain ⟨u1, hu1, _⟩ := exists_other_neighbor J hmin v0 v0
  obtain ⟨u2, hu2, hu21⟩ := exists_other_neighbor J hmin v0 u1
  obtain ⟨w1, hw1, hw1v⟩ := exists_other_neighbor J hmin u1 v0
  obtain ⟨w2, hw2, hw2v⟩ := exists_other_neighbor J hmin u2 v0
  have hw12 : w1 ≠ w2 := fun h => no_c4_pair J hc4 hw1v.symm hu21.symm hu1 hu2 hw1.symm (h ▸ hw2.symm)
  obtain ⟨u3, hu3, hu31⟩ := exists_other_neighbor J hmin w1 u1
  have hu32 : u3 ≠ u2 := fun h => no_c4_pair J hc4 hw1v.symm hu21.symm hu1 hu2 hw1.symm (h ▸ hu3)
  have hcol : ∀ a b : Fin r, J.Adj a b → c a ≠ c b := fun a b h => c.valid h
  have hcu1 : c u1 ≠ c v0 := (hcol v0 u1 hu1).symm
  have hcu2 : c u2 ≠ c v0 := (hcol v0 u2 hu2).symm
  have hcw1 : c w1 = c v0 := fin2_eq_of_ne_ne (hcol u1 w1 hw1).symm hcu1.symm
  have hcw2 : c w2 = c v0 := fin2_eq_of_ne_ne (hcol u2 w2 hw2).symm hcu2.symm
  have hcu3 : c u3 ≠ c v0 := by rw [← hcw1]; exact (hcol w1 u3 hu3).symm
  let S : Finset (Fin r) := {v0, w1, w2, u1, u2, u3}
  have hS : S.card = 6 := by
    have hne : ∀ x y : Fin r, c x ≠ c y → x ≠ y := fun x y h e => h (congrArg c e)
    have h1 : v0 ∉ ({w1, w2, u1, u2, u3} : Finset (Fin r)) := by
      simp [hw1v.symm, hw2v.symm, hne v0 u1 hcu1.symm, hne v0 u2 hcu2.symm, hne v0 u3 hcu3.symm]
    have h2 : w1 ∉ ({w2, u1, u2, u3} : Finset (Fin r)) := by
      simp [hw12, hne w1 u1 (hcw1 ▸ hcu1.symm), hne w1 u2 (hcw1 ▸ hcu2.symm), hne w1 u3 (hcw1 ▸ hcu3.symm)]
    have h3 : w2 ∉ ({u1, u2, u3} : Finset (Fin r)) := by
      simp [hne w2 u1 (hcw2 ▸ hcu1.symm), hne w2 u2 (hcw2 ▸ hcu2.symm), hne w2 u3 (hcw2 ▸ hcu3.symm)]
    have h4 : u1 ∉ ({u2, u3} : Finset (Fin r)) := by simp [hu21.symm, hu31.symm]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h4,
      Finset.card_pair hu32.symm]
  have hle : S.card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_card (Finset.subset_univ S)
  simp only [hS, Finset.card_univ, Fintype.card_fin] at hle
  exact hle

theorem eight_le_card_of_c4_c6_free {r : ℕ} (J : SimpleGraph (Fin r))
    (hbip : J.IsBipartite) (hconn : J.Connected) (hmin : ∀ v, 2 ≤ J.degree v)
    (hc4 : ¬ completeBipartiteGraph (Fin 2) (Fin 2) ⊑ J)
    (hc6 : ¬ cycleGraph 6 ⊑ J) : 8 ≤ r := by
  obtain ⟨v0⟩ := hconn.nonempty
  obtain ⟨c⟩ := hbip
  obtain ⟨u1, hu1, _⟩ := exists_other_neighbor J hmin v0 v0
  obtain ⟨u2, hu2, hu21⟩ := exists_other_neighbor J hmin v0 u1
  obtain ⟨w1, hw1, hw1v⟩ := exists_other_neighbor J hmin u1 v0
  obtain ⟨w2, hw2, hw2v⟩ := exists_other_neighbor J hmin u2 v0
  have hw12 : w1 ≠ w2 := fun h => no_c4_pair J hc4 hw1v.symm hu21.symm hu1 hu2 hw1.symm (h ▸ hw2.symm)
  obtain ⟨z1, hz1, hz1u1⟩ := exists_other_neighbor J hmin w1 u1
  have hz1u2 : z1 ≠ u2 := fun h => no_c4_pair J hc4 hw1v.symm hu21.symm hu1 hu2 hw1.symm (h ▸ hz1)
  obtain ⟨z2, hz2, hz2u2⟩ := exists_other_neighbor J hmin w2 u2
  have hz2u1 : z2 ≠ u1 := fun h => no_c4_pair J hc4 hw2v.symm hu21.symm hu1 hu2 (h ▸ hz2) hw2.symm
  have hcol : ∀ a b : Fin r, J.Adj a b → c a ≠ c b := fun a b h => c.valid h
  have hcu1 : c u1 ≠ c v0 := (hcol v0 u1 hu1).symm
  have hcu2 : c u2 ≠ c v0 := (hcol v0 u2 hu2).symm
  have hcw1 : c w1 = c v0 := fin2_eq_of_ne_ne (hcol u1 w1 hw1).symm hcu1.symm
  have hcw2 : c w2 = c v0 := fin2_eq_of_ne_ne (hcol u2 w2 hw2).symm hcu2.symm
  have hcz1 : c z1 ≠ c v0 := by rw [← hcw1]; exact (hcol w1 z1 hz1).symm
  have hcz2 : c z2 ≠ c v0 := by rw [← hcw2]; exact (hcol w2 z2 hz2).symm
  have hne : ∀ x y : Fin r, c x ≠ c y → x ≠ y := fun x y h e => h (congrArg c e)
  have h6card : ({v0, u1, w1, z1, w2, u2} : Finset (Fin r)).card = 6 := by
    have h1 : v0 ∉ ({u1, w1, z1, w2, u2} : Finset (Fin r)) := by
      simp [hw1v.symm, hw2v.symm, hne v0 u1 hcu1.symm, hne v0 u2 hcu2.symm, hne v0 z1 hcz1.symm]
    have h2 : u1 ∉ ({w1, z1, w2, u2} : Finset (Fin r)) := by
      simp [hu21.symm, hz1u1.symm, hne u1 w1 (hcw1 ▸ hcu1), hne u1 w2 (hcw2 ▸ hcu1)]
    have h3 : w1 ∉ ({z1, w2, u2} : Finset (Fin r)) := by
      simp [hw12, hne w1 z1 (hcw1 ▸ hcz1.symm), hne w1 u2 (hcw1 ▸ hcu2.symm)]
    have h4 : z1 ∉ ({w2, u2} : Finset (Fin r)) := by
      simp [hz1u2, hne z1 w2 (hcw2 ▸ hcz1)]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h4,
      Finset.card_pair (hne w2 u2 (hcw2 ▸ hcu2.symm))]
  have hz12 : z1 ≠ z2 := fun h =>
    no_c6_hex J hc6 hu1 hw1 hz1 (h ▸ hz2.symm) hw2.symm hu2.symm h6card
  obtain ⟨t, ht, htw1⟩ := exists_other_neighbor J hmin z1 w1
  have htv0 : t ≠ v0 := fun h => no_c4_pair J hc4 hw1v.symm hz1u1.symm hu1 (h ▸ ht.symm) hw1.symm hz1
  have htw2 : t ≠ w2 := fun h => no_c6_hex J hc6 hu1 hw1 hz1 (h ▸ ht) hw2.symm hu2.symm h6card
  have hct : c t = c v0 := fin2_eq_of_ne_ne (hcol z1 t ht).symm hcz1.symm
  let S : Finset (Fin r) := {v0, w1, w2, t, u1, u2, z1, z2}
  have hS : S.card = 8 := by
    have h1 : v0 ∉ ({w1, w2, t, u1, u2, z1, z2} : Finset (Fin r)) := by
      simp [hw1v.symm, hw2v.symm, htv0.symm, hne v0 u1 hcu1.symm, hne v0 u2 hcu2.symm,
        hne v0 z1 hcz1.symm, hne v0 z2 hcz2.symm]
    have h2 : w1 ∉ ({w2, t, u1, u2, z1, z2} : Finset (Fin r)) := by
      simp [hw12, htw1.symm, hne w1 u1 (hcw1 ▸ hcu1.symm), hne w1 u2 (hcw1 ▸ hcu2.symm),
        hne w1 z1 (hcw1 ▸ hcz1.symm), hne w1 z2 (hcw1 ▸ hcz2.symm)]
    have h3 : w2 ∉ ({t, u1, u2, z1, z2} : Finset (Fin r)) := by
      simp [htw2.symm, hne w2 u1 (hcw2 ▸ hcu1.symm), hne w2 u2 (hcw2 ▸ hcu2.symm),
        hne w2 z1 (hcw2 ▸ hcz1.symm), hne w2 z2 (hcw2 ▸ hcz2.symm)]
    have h4 : t ∉ ({u1, u2, z1, z2} : Finset (Fin r)) := by
      simp [hne t u1 (hct ▸ hcu1.symm), hne t u2 (hct ▸ hcu2.symm),
        hne t z1 (hct ▸ hcz1.symm), hne t z2 (hct ▸ hcz2.symm)]
    have h5 : u1 ∉ ({u2, z1, z2} : Finset (Fin r)) := by
      simp [hu21.symm, hz1u1.symm, hz2u1.symm]
    have h6 : u2 ∉ ({z1, z2} : Finset (Fin r)) := by
      simp [hz1u2.symm, hz2u2.symm]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h4,
      Finset.card_insert_of_notMem h5, Finset.card_insert_of_notMem h6,
      Finset.card_pair hz12]
  have hle : S.card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_card (Finset.subset_univ S)
  simp only [hS, Finset.card_univ, Fintype.card_fin] at hle
  exact hle

-- ### Part 4: Three disjoint girth hypotheses H1, H2, H3

/-- Girth-4 regime: `J` strictly contains `C_4 = K_{2,2}`, hence has `5 ≤ r`, `6 ≤ |E(J)|`, and
satisfies the affine-plane lower bound `p^3 ≤ extremalNumber (2 * p^2) J` for every prime `p`. -/
def H1 : Prop :=
  ∀ (r : ℕ) (J : SimpleGraph (Fin r)), J.IsBipartite → J.Connected →
    (∀ v, 2 ≤ J.degree v) → 5 ≤ r → 6 ≤ J.edgeFinset.card →
    completeBipartiteGraph (Fin 2) (Fin 2) ⊑ J →
    ¬ Nonempty (J ≃g completeBipartiteGraph (Fin 2) (Fin 2)) →
    (∀ p : ℕ, p.Prime → p ^ 3 ≤ extremalNumber (2 * p ^ 2) J) →
    Tendsto (fun n : ℕ => (extremalNumber n J : ℝ) / n) atTop atTop →
    ∃ α c : ℝ, α ∈ Set.Ioo 1 2 ∧ 0 < c ∧ IsEquivalent atTop
      (fun n : ℕ => (extremalNumber n J : ℝ)) (fun n => c * (n : ℝ) ^ α)

/-- Girth-6 regime: `J` is `C_4`-free and contains a `6`-cycle, hence has `6 ≤ r`, `6 ≤ |E(J)|`,
and satisfies Wenger's `W_3(p)` lower bound `p^4 ≤ extremalNumber (2 * p^3) J` for every prime `p`. -/
def H2 : Prop :=
  ∀ (r : ℕ) (J : SimpleGraph (Fin r)), J.IsBipartite → J.Connected →
    (∀ v, 2 ≤ J.degree v) → 6 ≤ r → 6 ≤ J.edgeFinset.card →
    ¬ completeBipartiteGraph (Fin 2) (Fin 2) ⊑ J →
    cycleGraph 6 ⊑ J →
    (∀ p : ℕ, p.Prime → p ^ 4 ≤ extremalNumber (2 * p ^ 3) J) →
    Tendsto (fun n : ℕ => (extremalNumber n J : ℝ) / n) atTop atTop →
    ∃ α c : ℝ, α ∈ Set.Ioo 1 2 ∧ 0 < c ∧ IsEquivalent atTop
      (fun n : ℕ => (extremalNumber n J : ℝ)) (fun n => c * (n : ℝ) ^ α)

/-- Girth-at-least-8 regime: `J` is both `C_4`-free and `C_6`-free, hence has `8 ≤ r` and
`8 ≤ |E(J)|`. -/
def H3 : Prop :=
  ∀ (r : ℕ) (J : SimpleGraph (Fin r)), J.IsBipartite → J.Connected →
    (∀ v, 2 ≤ J.degree v) → 8 ≤ r → 8 ≤ J.edgeFinset.card →
    ¬ completeBipartiteGraph (Fin 2) (Fin 2) ⊑ J →
    ¬ cycleGraph 6 ⊑ J →
    Tendsto (fun n : ℕ => (extremalNumber n J : ℝ) / n) atTop atTop →
    ∃ α c : ℝ, α ∈ Set.Ioo 1 2 ∧ 0 < c ∧ IsEquivalent atTop
      (fun n : ℕ => (extremalNumber n J : ℝ)) (fun n => c * (n : ℝ) ^ α)

-- ### Part 5: Main reduction proof

theorem main : H1 → H2 → H3 → OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1.H2 := by
  intro h1 h2 h3 r J hbip hconn hmin hnotiso hgrowth
  by_cases hc4 : completeBipartiteGraph (Fin 2) (Fin 2) ⊑ J
  · have hr5 : 5 ≤ r := five_le_card_of_c4_not_iso J hbip hc4 hnotiso
    have he6 : 6 ≤ J.edgeFinset.card := six_le_edges_of_five_le_bipartite J hbip hmin hr5
    have hlb : ∀ p : ℕ, p.Prime → p ^ 3 ≤ extremalNumber (2 * p ^ 2) J :=
      fun p hp => (cycle_four_extremal_subseq hp).trans hc4.extremalNumber_le
    exact h1 r J hbip hconn hmin hr5 he6 hc4 hnotiso hlb hgrowth
  · by_cases hc6 : cycleGraph 6 ⊑ J
    · have hr6 : 6 ≤ r := six_le_card_of_c4_free J hbip hconn hmin hc4
      have he6 : 6 ≤ J.edgeFinset.card := hr6.trans (card_le_edges_of_min_deg_two J hmin)
      have hlb : ∀ p : ℕ, p.Prime → p ^ 4 ≤ extremalNumber (2 * p ^ 3) J :=
        fun p hp => (cycle_six_extremal_subseq hp).trans hc6.extremalNumber_le
      exact h2 r J hbip hconn hmin hr6 he6 hc4 hc6 hlb hgrowth
    · have hr8 : 8 ≤ r := eight_le_card_of_c4_c6_free J hbip hconn hmin hc4 hc6
      have he8 : 8 ≤ J.edgeFinset.card := hr8.trans (card_le_edges_of_min_deg_two J hmin)
      exact h3 r J hbip hconn hmin hr8 he8 hc4 hc6 hgrowth

end OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1_H2_R1
