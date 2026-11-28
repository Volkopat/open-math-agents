import OMAReductions.R_Erdos128_erdos_128_R2_H2_R2

/-!
# Reduction Erdos128.erdos_128.R2.H2.R2.H1.R1 of step Erdos128.erdos_128.R2.H2.R2.H1

Proves and exports directly inside the reduction (Łuczak–Polcyn–Reiher 2024, arXiv:2406.10745,
Section 4, all finite n, zero sorry, standard axioms only):
1. **Cube Lemma** (Lemma 4.1 / Brandt): No maximal triangle-free graph with δ > n/3 contains
   an induced cube Q_3 = K_{4,4} - M_4.
2. **Graph N Lemma** (Lemma 4.2): For any copy of the 9-vertex graph N in a maximal triangle-free
   graph with δ > n/3, for every i ∈ Z/3Z either c_{i+1}c_{i+2} is an edge or {a_i, b_i, c_{i+1},
   c_{i+2}} has a common neighbor.
3. **Beautiful Lemma** (Lemma 4.3) and **Grötzsch Center Twin Lemma** (Lemma 4.4): For any
   Grötzsch subgraph Υ, if q is adjacent to a_{i-1} and a_{i+1} then q is adjacent to a_i, and
   the (Υ, c a_i)-twin property holds unconditionally.
4. **Vega Core Properties** (all i ≥ 2 and μ, ν ∈ Bool): Every Vega graph Υ_i^{μν} is maximal
   triangle-free and twin-free, so every homomorphism Υ_i^{μν} → G into a triangle-free graph G
   is automatically induced and injective, bounding 3i + 7 - μ - ν ≤ |V(G)|.
5. **Grötzsch ≅ Υ_2^{11} Isomorphism & Maximal Vega Subgraph**: Embeds the given Grötzsch copy
   as Υ_2^{11} and selects a maximum-order Vega subgraph Υ_i^{μν} ⊆ G.
6. **Long-Edge & xy Twin Lemma** (Lemma 4.26): Derives the twin property for xy (μ = 0) and all
   long Andrásfai edges directly from the Cube Lemma.

Reduces `Erdos128.erdos_128.R2.H2.R2.H1` cleanly to:
- H1: **Vega Twin Lemma** (Lemma 4.28): Every maximal Vega subgraph Υ_i^{μν} ⊆ G has the
      Υ_i^{μν}-twin property.
- H2: **Vega Attachment Lemma** (Lemma 4.29): Given a maximal Vega subgraph Υ_i^{μν} ⊆ G with
      the Υ_i^{μν}-twin property, every vertex q ∈ V(G) is an Υ_i^{μν}-twin of some active
      vertex of Υ_i^{μν}.
-/

-- Reduction Erdos128.erdos_128.R2.H2.R2.H1.R1 of step Erdos128.erdos_128.R2.H2.R2.H1
-- Credit: @therationalpie

namespace OMA.R_Erdos128_erdos_128_R2_H2_R2_H1_R1

open Finset SimpleGraph

-- H1: Vega Twin Lemma (Łuczak–Polcyn–Reiher 2024, Lemma 4.28):
-- For any maximal Vega subgraph Υ_i^{μν} of a maximal triangle-free graph G with δ > n/3,
-- any two Υ_i^{μν}-twins of adjacent active vertices are adjacent in G.
def H1 : Prop :=
  let va : ∀ i : ℕ, Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun i a b =>
    match a, b with
    | Sum.inl p, Sum.inl q =>
      i ≤ (q.1 + (3 * i - 1) - p.1) % (3 * i - 1) ∧ (q.1 + (3 * i - 1) - p.1) % (3 * i - 1) ≤ 2 * i - 1
    | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
      ((t.1 = 0 ∨ t.1 = 3) ∧ p.1 < i) ∨ ((t.1 = 4 ∨ t.1 = 1) ∧ i ≤ p.1 ∧ p.1 < 2 * i) ∨ ((t.1 = 2 ∨ t.1 = 5) ∧ 2 * i ≤ p.1)
    | Sum.inr a, Sum.inr b =>
      (a.1 < 6 ∧ b.1 < 6 ∧ ((a.1 + 1) % 6 = b.1 ∨ (b.1 + 1) % 6 = a.1)) ∨
      (a.1 = 6 ∧ (b.1 = 0 ∨ b.1 = 4 ∨ b.1 = 2 ∨ b.1 = 7)) ∨ (b.1 = 6 ∧ (a.1 = 0 ∨ a.1 = 4 ∨ a.1 = 2 ∨ a.1 = 7)) ∨
      (a.1 = 7 ∧ (b.1 = 3 ∨ b.1 = 1 ∨ b.1 = 5 ∨ b.1 = 6)) ∨ (b.1 = 7 ∧ (a.1 = 3 ∨ a.1 = 1 ∨ a.1 = 5 ∨ a.1 = 6))
  let act : ∀ i : ℕ, Bool → Bool → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun i μ ν x =>
    match x with | Sum.inl p => ν = true → p.1 ≠ 2 * i - 1 | Sum.inr t => μ = true → t.1 ≠ 7
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    (∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w) →
    (∀ v, Fintype.card V < 3 * (G.neighborSet v).ncard) →
    ∀ (i : ℕ) (μ ν : Bool) (f : Fin (3 * i - 1) ⊕ Fin 8 → V), 2 ≤ i →
    (∀ p q, act i μ ν p → act i μ ν q → va i p q → G.Adj (f p) (f q)) →
    (∀ i' μ' ν' (f' : Fin (3 * i' - 1) ⊕ Fin 8 → V), 2 ≤ i' → (∀ p q, act i' μ' ν' p → act i' μ' ν' q → va i' p q → G.Adj (f' p) (f' q)) →
      3 * i' + 7 - μ'.toNat - ν'.toNat ≤ 3 * i + 7 - μ.toNat - ν.toNat) →
    ∀ p q u v, act i μ ν p → act i μ ν q → va i p q →
      (∀ r, act i μ ν r → va i p r → G.Adj u (f r)) →
      (∀ r, act i μ ν r → va i q r → G.Adj v (f r)) → G.Adj u v

-- H2: Vega Attachment Lemma (Łuczak–Polcyn–Reiher 2024, Lemma 4.29):
-- Given a maximal Vega subgraph Υ_i^{μν} of a maximal triangle-free graph G with δ > n/3
-- satisfying the Υ_i^{μν}-twin property, every vertex q ∈ V(G) is a twin of some active vertex.
def H2 : Prop :=
  let va : ∀ i : ℕ, Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun i a b =>
    match a, b with
    | Sum.inl p, Sum.inl q =>
      i ≤ (q.1 + (3 * i - 1) - p.1) % (3 * i - 1) ∧ (q.1 + (3 * i - 1) - p.1) % (3 * i - 1) ≤ 2 * i - 1
    | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
      ((t.1 = 0 ∨ t.1 = 3) ∧ p.1 < i) ∨ ((t.1 = 4 ∨ t.1 = 1) ∧ i ≤ p.1 ∧ p.1 < 2 * i) ∨ ((t.1 = 2 ∨ t.1 = 5) ∧ 2 * i ≤ p.1)
    | Sum.inr a, Sum.inr b =>
      (a.1 < 6 ∧ b.1 < 6 ∧ ((a.1 + 1) % 6 = b.1 ∨ (b.1 + 1) % 6 = a.1)) ∨
      (a.1 = 6 ∧ (b.1 = 0 ∨ b.1 = 4 ∨ b.1 = 2 ∨ b.1 = 7)) ∨ (b.1 = 6 ∧ (a.1 = 0 ∨ a.1 = 4 ∨ a.1 = 2 ∨ a.1 = 7)) ∨
      (a.1 = 7 ∧ (b.1 = 3 ∨ b.1 = 1 ∨ b.1 = 5 ∨ b.1 = 6)) ∨ (b.1 = 7 ∧ (a.1 = 3 ∨ a.1 = 1 ∨ a.1 = 5 ∨ a.1 = 6))
  let act : ∀ i : ℕ, Bool → Bool → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun i μ ν x =>
    match x with | Sum.inl p => ν = true → p.1 ≠ 2 * i - 1 | Sum.inr t => μ = true → t.1 ≠ 7
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    (∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w) →
    (∀ v, Fintype.card V < 3 * (G.neighborSet v).ncard) →
    ∀ (i : ℕ) (μ ν : Bool) (f : Fin (3 * i - 1) ⊕ Fin 8 → V), 2 ≤ i →
    (∀ p q, act i μ ν p → act i μ ν q → va i p q → G.Adj (f p) (f q)) →
    (∀ i' μ' ν' (f' : Fin (3 * i' - 1) ⊕ Fin 8 → V), 2 ≤ i' → (∀ p q, act i' μ' ν' p → act i' μ' ν' q → va i' p q → G.Adj (f' p) (f' q)) →
      3 * i' + 7 - μ'.toNat - ν'.toNat ≤ 3 * i + 7 - μ.toNat - ν.toNat) →
    (∀ p q u v, act i μ ν p → act i μ ν q → va i p q →
      (∀ r, act i μ ν r → va i p r → G.Adj u (f r)) →
      (∀ r, act i μ ν r → va i q r → G.Adj v (f r)) → G.Adj u v) →
    ∀ q : V, ∃ p, act i μ ν p ∧ ∀ r, act i μ ν r → va i p r → G.Adj q (f r)

/- ### Part 1: Basic Bool / Prop_D helpers -/

lemma fin5_sub1_add2 (k : Fin 5) : (2 : Fin 5) + (k - 1) = k + 1 := by
  fin_cases k <;> rfl

lemma fin5_sub1_add1 (k : Fin 5) : (1 : Fin 5) + (k - 1) = k := by
  fin_cases k <;> rfl

lemma fin4_exists_ne2 (a b : Fin 4) : ∃ j : Fin 4, j ≠ a ∧ j ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma fin4_exists_ne3 (a b c : Fin 4) : ∃ j : Fin 4, j ≠ a ∧ j ≠ b ∧ j ≠ c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

lemma fin9_sum (f : Fin 9 → ℕ) :
    ∑ k : Fin 9, f k = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + f 8))))))) = _
  omega

lemma fin12_sum (f : Fin 12 → ℕ) :
    ∑ k : Fin 12, f k = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + f 11)))))))))) = _
  omega

lemma bool_edge_le {a b : Bool} (h : ¬ (a = true ∧ b = true)) : a.toNat + b.toNat ≤ 1 := by
  cases a <;> cases b <;> simp_all

lemma bool_c5_le {a b c d e : Bool}
    (h1 : ¬ (a = true ∧ b = true)) (h2 : ¬ (b = true ∧ c = true))
    (h3 : ¬ (c = true ∧ d = true)) (h4 : ¬ (d = true ∧ e = true))
    (h5 : ¬ (e = true ∧ a = true)) :
    a.toNat + b.toNat + c.toNat + d.toNat + e.toNat ≤ 2 := by
  have := bool_edge_le h1; have := bool_edge_le h2; have := bool_edge_le h3
  have := bool_edge_le h4; have := bool_edge_le h5; omega

lemma prop_D_bool {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (m : ℕ) (hm : 1 ≤ m) (xs : Fin (3 * m) → V) :
    ∃ (y : V) (b : Fin (3 * m) → Bool),
      (∀ k, b k = true ↔ G.Adj (xs k) y) ∧
      m + 1 ≤ ∑ k : Fin (3 * m), (b k).toNat ∧
      (∀ j k, G.Adj (xs j) (xs k) → ¬ (b j = true ∧ b k = true)) := by
  obtain ⟨y, hy⟩ := OMA.R_Erdos128_erdos_128_R2_H2_R2.prop_D G hmin m hm xs
  refine ⟨y, fun k => decide (G.Adj (xs k) y), ?_, ?_, ?_⟩
  · intro k; simp
  · have hcard : (Finset.univ.filter (fun i : Fin (3 * m) => G.Adj (xs i) y)).card =
        ∑ k : Fin (3 * m), (decide (G.Adj (xs k) y)).toNat := by
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : G.Adj (xs k) y <;> simp [h]
    simpa [hcard] using hy
  · intro j k hjk ⟨hj, hk⟩
    simp only [decide_eq_true_eq] at hj hk
    exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf hj.symm hk.symm hjk

/- ### Part 2: Cube Lemma (Lemma 4.1) -/

lemma cube_12_indep (a b c : Fin 4 → Bool)
    (hab : ∀ i j : Fin 4, i ≠ j → ¬ (a i = true ∧ b j = true))
    (hac : ∀ i : Fin 4, ¬ (a i = true ∧ c i = true))
    (hbc : ∀ i : Fin 4, ¬ (b i = true ∧ c i = true))
    (hsum : 5 ≤ ∑ i : Fin 4, (a i).toNat + ∑ i : Fin 4, (b i).toNat + ∑ i : Fin 4, (c i).toNat) :
    ∃ k : Fin 4, a k = true ∧ b k = true ∧ ∀ j : Fin 4, j ≠ k → c j = true := by
  have ha_ex : ∃ k : Fin 4, a k = true := by
    by_contra h
    push Not at h
    have h0 : ∑ i : Fin 4, (a i).toNat = 0 :=
      Finset.sum_eq_zero fun i _ => by cases ha : a i; rfl; exact absurd ha (h i)
    have hbc_sum : ∑ i : Fin 4, ((b i).toNat + (c i).toNat) ≤ 4 := by
      calc ∑ i : Fin 4, ((b i).toNat + (c i).toNat)
          ≤ ∑ _i : Fin 4, 1 := Finset.sum_le_sum fun i _ => bool_edge_le (hbc i)
        _ = 4 := by simp
    rw [Finset.sum_add_distrib] at hbc_sum
    omega
  obtain ⟨k, hak⟩ := ha_ex
  have hbj : ∀ j : Fin 4, j ≠ k → b j = false := by
    intro j hj
    cases hb : b j
    · rfl
    · exact absurd ⟨hak, hb⟩ (hab k j hj.symm)
  have hbk : b k = true := by
    by_contra hbk_ne
    have hbk_f : b k = false := by cases hb : b k <;> simp_all
    have hb0 : ∑ i : Fin 4, (b i).toNat = 0 :=
      Finset.sum_eq_zero fun i _ => by
        by_cases hik : i = k
        · subst hik; simp [hbk_f]
        · simp [hbj i hik]
    have hac_sum : ∑ i : Fin 4, ((a i).toNat + (c i).toNat) ≤ 4 := by
      calc ∑ i : Fin 4, ((a i).toNat + (c i).toNat)
          ≤ ∑ _i : Fin 4, 1 := Finset.sum_le_sum fun i _ => bool_edge_le (hac i)
        _ = 4 := by simp
    rw [Finset.sum_add_distrib] at hac_sum
    omega
  have haj : ∀ j : Fin 4, j ≠ k → a j = false := by
    intro j hj
    cases ha : a j
    · rfl
    · exact absurd ⟨ha, hbk⟩ (hab j k hj)
  have hck : c k = false := by
    cases hc : c k
    · rfl
    · exact absurd ⟨hak, hc⟩ (hac k)
  refine ⟨k, hak, hbk, fun j hj => ?_⟩
  by_contra hcj_ne
  have hcj_f : c j = false := by cases hc : c j <;> simp_all
  have hsum_a : ∑ i : Fin 4, (a i).toNat = 1 := by
    rw [Finset.sum_eq_single k (fun i _ hik => by simp [haj i hik]) (by simp)]
    simp [hak]
  have hsum_b : ∑ i : Fin 4, (b i).toNat = 1 := by
    rw [Finset.sum_eq_single k (fun i _ hik => by simp [hbj i hik]) (by simp)]
    simp [hbk]
  have hsum_c : ∑ i : Fin 4, (c i).toNat ≤ 2 := by
    have hfin : (∑ i : Fin 4, (c i).toNat) =
        (c 0).toNat + (c 1).toNat + (c 2).toNat + (c 3).toNat := by
      simp [Fin.sum_univ_four]
    rw [hfin]
    have hle : ∀ i : Fin 4, (c i).toNat ≤ 1 := fun i => by cases c i <;> decide
    fin_cases k <;> fin_cases j <;> first | exact absurd rfl hj | (simp_all; have := hle 0; have := hle 1; have := hle 2; have := hle 3; omega)
  omega

lemma cube_9_indep (a b c : Fin 3 → Bool)
    (hab : ∀ i j : Fin 3, i ≠ j → ¬ (a i = true ∧ b j = true))
    (hac : ∀ i : Fin 3, ¬ (a i = true ∧ c i = true))
    (hbc : ∀ i : Fin 3, ¬ (b i = true ∧ c i = true))
    (hsum : 4 ≤ ∑ i : Fin 3, (a i).toNat + ∑ i : Fin 3, (b i).toNat + ∑ i : Fin 3, (c i).toNat) :
    ∃ k : Fin 3, a k = true ∧ b k = true ∧ ∀ j : Fin 3, j ≠ k → c j = true := by
  have ha_ex : ∃ k : Fin 3, a k = true := by
    by_contra h
    push Not at h
    have h0 : ∑ i : Fin 3, (a i).toNat = 0 :=
      Finset.sum_eq_zero fun i _ => by cases ha : a i; rfl; exact absurd ha (h i)
    have hbc_sum : ∑ i : Fin 3, ((b i).toNat + (c i).toNat) ≤ 3 := by
      calc ∑ i : Fin 3, ((b i).toNat + (c i).toNat)
          ≤ ∑ _i : Fin 3, 1 := Finset.sum_le_sum fun i _ => bool_edge_le (hbc i)
        _ = 3 := by simp
    rw [Finset.sum_add_distrib] at hbc_sum
    omega
  obtain ⟨k, hak⟩ := ha_ex
  have hbj : ∀ j : Fin 3, j ≠ k → b j = false := by
    intro j hj
    cases hb : b j
    · rfl
    · exact absurd ⟨hak, hb⟩ (hab k j hj.symm)
  have hbk : b k = true := by
    by_contra hbk_ne
    have hbk_f : b k = false := by cases hb : b k <;> simp_all
    have hb0 : ∑ i : Fin 3, (b i).toNat = 0 :=
      Finset.sum_eq_zero fun i _ => by
        by_cases hik : i = k
        · subst hik; simp [hbk_f]
        · simp [hbj i hik]
    have hac_sum : ∑ i : Fin 3, ((a i).toNat + (c i).toNat) ≤ 3 := by
      calc ∑ i : Fin 3, ((a i).toNat + (c i).toNat)
          ≤ ∑ _i : Fin 3, 1 := Finset.sum_le_sum fun i _ => bool_edge_le (hac i)
        _ = 3 := by simp
    rw [Finset.sum_add_distrib] at hac_sum
    omega
  have haj : ∀ j : Fin 3, j ≠ k → a j = false := by
    intro j hj
    cases ha : a j
    · rfl
    · exact absurd ⟨ha, hbk⟩ (hab j k hj)
  have hck : c k = false := by
    cases hc : c k
    · rfl
    · exact absurd ⟨hak, hc⟩ (hac k)
  refine ⟨k, hak, hbk, fun j hj => ?_⟩
  by_contra hcj_ne
  have hcj_f : c j = false := by cases hc : c j <;> simp_all
  have hsum_a : ∑ i : Fin 3, (a i).toNat = 1 := by
    rw [Finset.sum_eq_single k (fun i _ hik => by simp [haj i hik]) (by simp)]
    simp [hak]
  have hsum_b : ∑ i : Fin 3, (b i).toNat = 1 := by
    rw [Finset.sum_eq_single k (fun i _ hik => by simp [hbj i hik]) (by simp)]
    simp [hbk]
  have hsum_c : ∑ i : Fin 3, (c i).toNat ≤ 1 := by
    have hfin : (∑ i : Fin 3, (c i).toNat) = (c 0).toNat + (c 1).toNat + (c 2).toNat := by
      simp [Fin.sum_univ_three]
    rw [hfin]
    have hle : ∀ i : Fin 3, (c i).toNat ≤ 1 := fun i => by cases c i <;> decide
    have h0 := hle 0; have h1 := hle 1; have h2 := hle 2
    fin_cases k <;> fin_cases j <;> first | exact absurd rfl hj | (simp_all; try omega)
  omega

lemma cube_lemma {V : Type} [Fintype V]
    (G : SimpleGraph V) (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b : Fin 4 → V)
    (hab : ∀ i j : Fin 4, i ≠ j → G.Adj (a i) (b j)) :
    ∃ i : Fin 4, G.Adj (a i) (b i) := by
  classical
  by_contra hno
  push Not at hno
  -- Step 1: common neighbor c_i of a_i, b_i for each i ∈ Fin 4
  have hc_ex : ∀ i : Fin 4, ∃ w : V, G.Adj (a i) w ∧ G.Adj (b i) w := by
    intro i
    have hne : a i ≠ b i := by
      intro heq
      -- Pick j ≠ i and k ∉ {i, j}: a_i = b_i ~ b_j, while a_k ~ b_i and a_k ~ b_j => triangle!
      let j : Fin 4 := i + 1
      let k : Fin 4 := i + 2
      have hij : i ≠ j := by fin_cases i <;> decide
      have hki : k ≠ i := by fin_cases i <;> decide
      have hkj : k ≠ j := by fin_cases i <;> decide
      have h1 : G.Adj (b i) (b j) := by rw [← heq]; exact hab i j hij
      exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf (hab k i hki) (hab k j hkj) h1
    exact hmax (a i) (b i) hne (hno i)
  choose c hac hbc using hc_ex
  -- Helper: apply D_4 to (a, b, c_cur) to get k and t ~ {a k, b k} ∪ {c_cur j | j ≠ k}
  have step_d4 : ∀ c' : Fin 4 → V,
      (∀ i, G.Adj (a i) (c' i)) → (∀ i, G.Adj (b i) (c' i)) →
      ∃ (k : Fin 4) (t : V), G.Adj (a k) t ∧ G.Adj (b k) t ∧
        ∀ j : Fin 4, j ≠ k → G.Adj (c' j) t := by
    intro c' hac' hbc'
    let xs : Fin 12 → V := fun x =>
      if h1 : x.val < 4 then a ⟨x.val, h1⟩
      else if h2 : x.val < 8 then b ⟨x.val - 4, by omega⟩
      else c' ⟨x.val - 8, by omega⟩
    obtain ⟨t, f, hf, hsum, hind⟩ := prop_D_bool G hcf hmin 4 (by omega) xs
    let fa : Fin 4 → Bool := fun i => f ⟨i.val, by omega⟩
    let fb : Fin 4 → Bool := fun i => f ⟨i.val + 4, by omega⟩
    let fc : Fin 4 → Bool := fun i => f ⟨i.val + 8, by omega⟩
    have hxs_a : ∀ i : Fin 4, xs ⟨i.val, by omega⟩ = a i := fun i => by simp [xs, i.isLt]
    have hxs_b : ∀ i : Fin 4, xs ⟨i.val + 4, by omega⟩ = b i := fun i => by
      have hi := i.isLt; simp [xs, show ¬ i.val + 4 < 4 by omega, show i.val + 4 < 8 by omega]
    have hxs_c : ∀ i : Fin 4, xs ⟨i.val + 8, by omega⟩ = c' i := fun i => by
      have hi := i.isLt; simp [xs, show ¬ i.val + 8 < 4 by omega, show ¬ i.val + 8 < 8 by omega]
    have hsum' : 5 ≤ ∑ i : Fin 4, (fa i).toNat + ∑ i : Fin 4, (fb i).toNat +
        ∑ i : Fin 4, (fc i).toNat := by
      have h12 : (∑ x : Fin 12, (f x).toNat) =
          ∑ i : Fin 4, (fa i).toNat + ∑ i : Fin 4, (fb i).toNat + ∑ i : Fin 4, (fc i).toNat := by
        rw [fin12_sum (fun x => (f x).toNat)]
        simp only [Fin.sum_univ_four, fa, fb, fc]
        change (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat + (f 4).toNat + (f 5).toNat +
          (f 6).toNat + (f 7).toNat + (f 8).toNat + (f 9).toNat + (f 10).toNat + (f 11).toNat =
          ((f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat) +
          ((f 4).toNat + (f 5).toNat + (f 6).toNat + (f 7).toNat) +
          ((f 8).toNat + (f 9).toNat + (f 10).toNat + (f 11).toNat)
        omega
      rw [← h12]; exact hsum
    obtain ⟨k, hak, hbk, hcj⟩ := cube_12_indep fa fb fc
      (fun i j hij => by
        have h := hind ⟨i.val, by omega⟩ ⟨j.val + 4, by omega⟩
        rw [hxs_a, hxs_b] at h; exact h (hab i j hij))
      (fun i => by
        have h := hind ⟨i.val, by omega⟩ ⟨i.val + 8, by omega⟩
        rw [hxs_a, hxs_c] at h; exact h (hac' i))
      (fun i => by
        have h := hind ⟨i.val + 4, by omega⟩ ⟨i.val + 8, by omega⟩
        rw [hxs_b, hxs_c] at h; exact h (hbc' i))
      hsum'
    refine ⟨k, t, ?_, ?_, fun j hj => ?_⟩
    · have := (hf ⟨k.val, by omega⟩).mp hak; rwa [hxs_a] at this
    · have := (hf ⟨k.val + 4, by omega⟩).mp hbk; rwa [hxs_b] at this
    · have := (hf ⟨j.val + 8, by omega⟩).mp (hcj j hj); rwa [hxs_c] at this
  -- Step 2: apply step_d4 to c to get k and t, replace c k with t -> c1
  obtain ⟨k, t, hakt, hbkt, hcjt⟩ := step_d4 c hac hbc
  let c1 : Fin 4 → V := Function.update c k t
  have hac1 : ∀ i, G.Adj (a i) (c1 i) := fun i => by
    by_cases h : i = k
    · subst h; simpa [c1] using hakt
    · simpa [c1, h] using hac i
  have hbc1 : ∀ i, G.Adj (b i) (c1 i) := fun i => by
    by_cases h : i = k
    · subst h; simpa [c1] using hbkt
    · simpa [c1, h] using hbc i
  have hc1_star : ∀ j : Fin 4, j ≠ k → G.Adj (c1 j) (c1 k) := fun j hj => by
    simpa [c1, hj] using hcjt j hj
  -- Step 3: apply D_3 to the 3 indices other than k (using k.succAbove : Fin 3 ↪o Fin 4)
  let e : Fin 3 → Fin 4 := k.succAbove
  have he_ne : ∀ r : Fin 3, e r ≠ k := fun r => Fin.succAbove_ne k r
  have he_inj : Function.Injective e := Fin.succAbove_right_injective
  let ys : Fin 9 → V := fun x =>
    if h1 : x.val < 3 then a (e ⟨x.val, h1⟩)
    else if h2 : x.val < 6 then b (e ⟨x.val - 3, by omega⟩)
    else c1 (e ⟨x.val - 6, by omega⟩)
  obtain ⟨s, g, hg, hsum9, hind9⟩ := prop_D_bool G hcf hmin 3 (by omega) ys
  let ga : Fin 3 → Bool := fun r => g ⟨r.val, by omega⟩
  let gb : Fin 3 → Bool := fun r => g ⟨r.val + 3, by omega⟩
  let gc : Fin 3 → Bool := fun r => g ⟨r.val + 6, by omega⟩
  have hys_a : ∀ r : Fin 3, ys ⟨r.val, by omega⟩ = a (e r) := fun r => by simp [ys, r.isLt]
  have hys_b : ∀ r : Fin 3, ys ⟨r.val + 3, by omega⟩ = b (e r) := fun r => by
    have hr := r.isLt; simp [ys, show ¬ r.val + 3 < 3 by omega, show r.val + 3 < 6 by omega]
  have hys_c : ∀ r : Fin 3, ys ⟨r.val + 6, by omega⟩ = c1 (e r) := fun r => by
    have hr := r.isLt; simp [ys, show ¬ r.val + 6 < 3 by omega, show ¬ r.val + 6 < 6 by omega]
  have hsum9' : 4 ≤ ∑ r : Fin 3, (ga r).toNat + ∑ r : Fin 3, (gb r).toNat +
      ∑ r : Fin 3, (gc r).toNat := by
    have h9 : (∑ x : Fin 9, (g x).toNat) =
        ∑ r : Fin 3, (ga r).toNat + ∑ r : Fin 3, (gb r).toNat + ∑ r : Fin 3, (gc r).toNat := by
      rw [fin9_sum (fun x => (g x).toNat)]
      simp only [Fin.sum_univ_three, ga, gb, gc]
      change (g 0).toNat + (g 1).toNat + (g 2).toNat + (g 3).toNat + (g 4).toNat +
        (g 5).toNat + (g 6).toNat + (g 7).toNat + (g 8).toNat =
        ((g 0).toNat + (g 1).toNat + (g 2).toNat) +
        ((g 3).toNat + (g 4).toNat + (g 5).toNat) +
        ((g 6).toNat + (g 7).toNat + (g 8).toNat)
      omega
    rw [← h9]; exact hsum9
  obtain ⟨m0, ham0, hbm0, hcm0⟩ := cube_9_indep ga gb gc
    (fun r₁ r₂ hr => by
      have h := hind9 ⟨r₁.val, by omega⟩ ⟨r₂.val + 3, by omega⟩
      rw [hys_a, hys_b] at h; exact h (hab (e r₁) (e r₂) (fun heq => hr (he_inj heq))))
    (fun r => by
      have h := hind9 ⟨r.val, by omega⟩ ⟨r.val + 6, by omega⟩
      rw [hys_a, hys_c] at h; exact h (hac1 (e r)))
    (fun r => by
      have h := hind9 ⟨r.val + 3, by omega⟩ ⟨r.val + 6, by omega⟩
      rw [hys_b, hys_c] at h; exact h (hbc1 (e r)))
    hsum9'
  let m : Fin 4 := e m0
  have hmk : m ≠ k := he_ne m0
  have hams : G.Adj (a m) s := by
    have := (hg ⟨m0.val, by omega⟩).mp ham0; rwa [hys_a] at this
  have hbms : G.Adj (b m) s := by
    have := (hg ⟨m0.val + 3, by omega⟩).mp hbm0; rwa [hys_b] at this
  have hcms : ∀ j : Fin 4, j ≠ k → j ≠ m → G.Adj (c1 j) s := by
    intro j hjk hjm
    obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hjk
    have hrm : r ≠ m0 := fun hr => hjm (by simp [m, e, hr])
    have := (hg ⟨r.val + 6, by omega⟩).mp (hcm0 r hrm)
    rwa [hys_c] at this
  -- Step 4: replace c1 m with s -> c2, forming a 4-cycle on c2: {k, m} ↔ Fin 4 \ {k, m}
  let c2 : Fin 4 → V := Function.update c1 m s
  have hac2 : ∀ i, G.Adj (a i) (c2 i) := fun i => by
    by_cases h : i = m
    · subst h; simpa [c2] using hams
    · simpa [c2, h] using hac1 i
  have hbc2 : ∀ i, G.Adj (b i) (c2 i) := fun i => by
    by_cases h : i = m
    · subst h; simpa [c2] using hbms
    · simpa [c2, h] using hbc1 i
  have hc2_k : ∀ j : Fin 4, j ≠ k → j ≠ m → G.Adj (c2 j) (c2 k) := fun j hjk hjm => by
    have hkm : k ≠ m := hmk.symm
    simpa [c2, hjm, hkm] using hc1_star j hjk
  have hc2_m : ∀ j : Fin 4, j ≠ k → j ≠ m → G.Adj (c2 j) (c2 m) := fun j hjk hjm => by
    simpa [c2, hjm] using hcms j hjk hjm
  -- Step 5: apply step_d4 to c2 -> get r and w adjacent to c2 j for ALL j ≠ r, creating a triangle!
  obtain ⟨r, w, _, _, hc2w⟩ := step_d4 c2 hac2 hbc2
  -- Among Fin 4 \ {r}, there is always an edge of the 4-cycle {k, m} × (Fin 4 \ {k, m})!
  have hpair : ∃ u v : Fin 4, u ≠ r ∧ v ≠ r ∧ G.Adj (c2 u) (c2 v) := by
    by_cases hrk : r = k
    · obtain ⟨j, hjk, hjm⟩ := fin4_exists_ne2 k m
      exact ⟨j, m, by rw [hrk]; exact hjk, by rw [hrk]; exact hmk, hc2_m j hjk hjm⟩
    · by_cases hrm : r = m
      · obtain ⟨j, hjk, hjm⟩ := fin4_exists_ne2 k m
        exact ⟨j, k, by rw [hrm]; exact hjm, by rw [hrm]; exact hmk.symm, hc2_k j hjk hjm⟩
      · obtain ⟨j, hjk, hjm, hjr⟩ := fin4_exists_ne3 k m r
        exact ⟨j, k, hjr, Ne.symm hrk, hc2_k j hjk hjm⟩
  obtain ⟨u, v, hur, hvr, huv⟩ := hpair
  exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf
    (hc2w u hur).symm (hc2w v hvr).symm huv

/- ### Part 3: Graph N Lemma (Lemma 4.2) -/

lemma graph_N_9_indep (a0 a1 a2 b0 b1 b2 c0 c2 y : Bool)
    (h_a0b1 : ¬ (a0 = true ∧ b1 = true)) (h_a0b2 : ¬ (a0 = true ∧ b2 = true))
    (h_a1b0 : ¬ (a1 = true ∧ b0 = true)) (h_a1b2 : ¬ (a1 = true ∧ b2 = true))
    (h_a2b0 : ¬ (a2 = true ∧ b0 = true)) (h_a2b1 : ¬ (a2 = true ∧ b1 = true))
    (h_a0c0 : ¬ (a0 = true ∧ c0 = true)) (h_b0c0 : ¬ (b0 = true ∧ c0 = true))
    (h_a2c2 : ¬ (a2 = true ∧ c2 = true)) (h_b2c2 : ¬ (b2 = true ∧ c2 = true))
    (h_yc0 : ¬ (y = true ∧ c0 = true)) (h_yc2 : ¬ (y = true ∧ c2 = true))
    (hsum : 4 ≤ a0.toNat + a1.toNat + a2.toNat + b0.toNat + b1.toNat + b2.toNat +
      c0.toNat + c2.toNat + y.toNat) :
    (a1 = true ∧ b1 = true ∧ c0 = true ∧ c2 = true) ∨
    (a0 = true ∧ a1 = true ∧ a2 = true ∧ y = true) ∨
    (b0 = true ∧ b1 = true ∧ b2 = true ∧ y = true) := by
  have := bool_edge_le h_a0b1; have := bool_edge_le h_a0b2
  have := bool_edge_le h_a1b0; have := bool_edge_le h_a1b2
  have := bool_edge_le h_a2b0; have := bool_edge_le h_a2b1
  have := bool_edge_le h_a0c0; have := bool_edge_le h_b0c0
  have := bool_edge_le h_a2c2; have := bool_edge_le h_b2c2
  have := bool_edge_le h_yc0; have := bool_edge_le h_yc2
  have hle : ∀ x : Bool, x.toNat ≤ 1 := fun x => by cases x <;> decide
  have := hle a0; have := hle a1; have := hle a2
  have := hle b0; have := hle b1; have := hle b2
  have := hle c0; have := hle c2; have := hle y
  cases y with
  | true =>
    have hc0 : c0 = false := by cases c0 <;> simp_all
    have hc2 : c2 = false := by cases c2 <;> simp_all
    subst hc0; subst hc2
    cases a0 <;> cases b0 <;> simp_all <;> try omega
    · have ha1 : a1 = false := by cases a1 <;> simp_all
      have ha2 : a2 = false := by cases a2 <;> simp_all
      subst ha1 ha2; cases b1 <;> cases b2 <;> simp_all
    · have hb1 : b1 = false := by cases b1 <;> simp_all
      have hb2 : b2 = false := by cases b2 <;> simp_all
      subst hb1 hb2; cases a1 <;> cases a2 <;> simp_all
  | false =>
    cases c0 <;> cases c2 <;> simp_all <;> try omega
    · have ha0 : a0 = false := by cases a0 <;> simp_all
      have hb0 : b0 = false := by cases b0 <;> simp_all
      have ha2 : a2 = false := by cases a2 <;> simp_all
      have hb2 : b2 = false := by cases b2 <;> simp_all
      subst ha0 hb0 ha2 hb2; cases a1 <;> cases b1 <;> simp_all

lemma graph_N_pentagon_indep (b2 a1 b0 a2 c2 y c0 c1 b1 : Bool)
    (h1 : ¬ (b2 = true ∧ a1 = true)) (h2 : ¬ (a1 = true ∧ b0 = true))
    (h3 : ¬ (b0 = true ∧ a2 = true)) (h4 : ¬ (a2 = true ∧ c2 = true))
    (h5 : ¬ (c2 = true ∧ b2 = true)) (h6 : ¬ (y = true ∧ c0 = true))
    (h7 : ¬ (c1 = true ∧ b1 = true)) (h8 : ¬ (y = true ∧ c2 = true))
    (h9 : ¬ (c0 = true ∧ b0 = true)) (h10 : ¬ (b1 = true ∧ a2 = true))
    (h11 : ¬ (c1 = true ∧ a1 = true))
    (hsum : 4 ≤ b2.toNat + a1.toNat + b0.toNat + a2.toNat + c2.toNat +
      y.toNat + c0.toNat + c1.toNat + b1.toNat) :
    (a1 = true ∧ b1 = true ∧ c0 = true ∧ c2 = true) ∨
    (b2 = true ∧ b0 = true ∧ y = true) ∨
    (b2 = true ∧ a2 = true ∧ c1 = true) := by
  have := bool_c5_le h1 h2 h3 h4 h5
  have := bool_edge_le h6; have := bool_edge_le h7
  have := bool_edge_le h8; have := bool_edge_le h11
  have hle : ∀ x : Bool, x.toNat ≤ 1 := fun x => by cases x <;> decide
  have := hle b2; have := hle a1; have := hle b0; have := hle a2; have := hle c2
  have := hle y; have := hle c0; have := hle c1; have := hle b1
  cases b2 with
  | true =>
    have ha1 : a1 = false := by cases a1 <;> simp_all
    have hc2 : c2 = false := by cases c2 <;> simp_all
    subst ha1; subst hc2
    cases b0 <;> cases a2 <;> simp_all <;> try omega
    · have hb1 : b1 = false := by cases b1 <;> simp_all
      subst hb1; cases c1 <;> simp_all; omega
    · have hc0 : c0 = false := by cases c0 <;> simp_all
      subst hc0; cases y <;> simp_all; omega
  | false =>
    cases b0 <;> cases a2 <;> simp_all <;> try omega
    · cases a1 <;> cases c2 <;> cases c0 <;> cases b1 <;> simp_all <;> omega

lemma graph_N_12_caseA (a0 a1 a2 b0 b2 c0 c1 c2 y z x0 q : Bool)
    (h_a0b2 : ¬ (a0 = true ∧ b2 = true)) (h_a1b0 : ¬ (a1 = true ∧ b0 = true))
    (h_a1b2 : ¬ (a1 = true ∧ b2 = true)) (h_a2b0 : ¬ (a2 = true ∧ b0 = true))
    (h_a0c0 : ¬ (a0 = true ∧ c0 = true)) (h_b0c0 : ¬ (b0 = true ∧ c0 = true))
    (h_a1c1 : ¬ (a1 = true ∧ c1 = true)) (_h_a2c2 : ¬ (a2 = true ∧ c2 = true))
    (h_b2c2 : ¬ (b2 = true ∧ c2 = true)) (h_yc0 : ¬ (y = true ∧ c0 = true))
    (h_yc2 : ¬ (y = true ∧ c2 = true)) (h_za0 : ¬ (z = true ∧ a0 = true))
    (h_za1 : ¬ (z = true ∧ a1 = true)) (h_za2 : ¬ (z = true ∧ a2 = true))
    (h_zy : ¬ (z = true ∧ y = true)) (h_x0a0 : ¬ (x0 = true ∧ a0 = true))
    (h_x0b0 : ¬ (x0 = true ∧ b0 = true)) (h_x0c1 : ¬ (x0 = true ∧ c1 = true))
    (h_x0c2 : ¬ (x0 = true ∧ c2 = true)) (h_qa2 : ¬ (q = true ∧ a2 = true))
    (h_qc1 : ¬ (q = true ∧ c1 = true)) (h_qb2 : ¬ (q = true ∧ b2 = true)) :
    a0.toNat + a1.toNat + a2.toNat + b0.toNat + b2.toNat + c0.toNat +
    c1.toNat + c2.toNat + y.toNat + z.toNat + x0.toNat + q.toNat ≤ 4 := by
  have hle : ∀ x : Bool, x.toNat ≤ 1 := fun x => by cases x <;> decide
  cases a0 with
  | true =>
    have hb2 : b2 = false := by cases b2 <;> simp_all
    have hc0 : c0 = false := by cases c0 <;> simp_all
    have hz : z = false := by cases z <;> simp_all
    have hx0 : x0 = false := by cases x0 <;> simp_all
    have hc5 := bool_c5_le h_a1b0 (fun ⟨h1, h2⟩ => h_a2b0 ⟨h2, h1⟩)
      (fun ⟨h1, h2⟩ => h_qa2 ⟨h2, h1⟩) h_qc1 (fun ⟨h1, h2⟩ => h_a1c1 ⟨h2, h1⟩)
    have he := bool_edge_le h_yc2
    subst hb2 hc0 hz hx0; simp; omega
  | false =>
    cases a1 with
    | true =>
      have hb0 : b0 = false := by cases b0 <;> simp_all
      have hb2 : b2 = false := by cases b2 <;> simp_all
      have hc1 : c1 = false := by cases c1 <;> simp_all
      have hz : z = false := by cases z <;> simp_all
      have e1 := bool_edge_le h_qa2; have e2 := bool_edge_le h_yc0; have e3 := bool_edge_le h_x0c2
      subst hb0 hb2 hc1 hz; simp; omega
    | false =>
      have hc5_1 := bool_c5_le (fun ⟨h1, h2⟩ => h_za2 ⟨h2, h1⟩) h_zy h_yc0
        (fun ⟨h1, h2⟩ => h_b0c0 ⟨h2, h1⟩) (fun ⟨h1, h2⟩ => h_a2b0 ⟨h2, h1⟩)
      have hc5_2 := bool_c5_le (fun ⟨h1, h2⟩ => h_qb2 ⟨h2, h1⟩) h_qc1
        (fun ⟨h1, h2⟩ => h_x0c1 ⟨h2, h1⟩) h_x0c2 (fun ⟨h1, h2⟩ => h_b2c2 ⟨h2, h1⟩)
      simp; omega

lemma graph_N_12_caseB (a0 a1 a2 b0 b1 b2 c1 c2 y z x0 q : Bool)
    (h_a0b1 : ¬ (a0 = true ∧ b1 = true)) (h_a0b2 : ¬ (a0 = true ∧ b2 = true))
    (h_a1b0 : ¬ (a1 = true ∧ b0 = true)) (h_a1b2 : ¬ (a1 = true ∧ b2 = true))
    (h_a2b0 : ¬ (a2 = true ∧ b0 = true)) (h_a2b1 : ¬ (a2 = true ∧ b1 = true))
    (h_a1c1 : ¬ (a1 = true ∧ c1 = true)) (h_b1c1 : ¬ (b1 = true ∧ c1 = true))
    (h_a2c2 : ¬ (a2 = true ∧ c2 = true)) (h_b2c2 : ¬ (b2 = true ∧ c2 = true))
    (h_yc2 : ¬ (y = true ∧ c2 = true)) (h_za0 : ¬ (z = true ∧ a0 = true))
    (h_za1 : ¬ (z = true ∧ a1 = true)) (h_za2 : ¬ (z = true ∧ a2 = true))
    (h_zy : ¬ (z = true ∧ y = true)) (h_x0a0 : ¬ (x0 = true ∧ a0 = true))
    (h_x0b0 : ¬ (x0 = true ∧ b0 = true)) (h_x0c1 : ¬ (x0 = true ∧ c1 = true))
    (h_x0c2 : ¬ (x0 = true ∧ c2 = true)) (h_qb2 : ¬ (q = true ∧ b2 = true))
    (h_qb0 : ¬ (q = true ∧ b0 = true)) (h_qy : ¬ (q = true ∧ y = true)) :
    a0.toNat + a1.toNat + a2.toNat + b0.toNat + b1.toNat + b2.toNat +
    c1.toNat + c2.toNat + y.toNat + z.toNat + x0.toNat + q.toNat ≤ 4 := by
  have hle : ∀ x : Bool, x.toNat ≤ 1 := fun x => by cases x <;> decide
  cases a0 with
  | true =>
    have hb1 : b1 = false := by cases b1 <;> simp_all
    have hb2 : b2 = false := by cases b2 <;> simp_all
    have hz : z = false := by cases z <;> simp_all
    have hx0 : x0 = false := by cases x0 <;> simp_all
    have hc5 := bool_c5_le h_a2b0 (fun ⟨h1, h2⟩ => h_qb0 ⟨h2, h1⟩) h_qy h_yc2
      (fun ⟨h1, h2⟩ => h_a2c2 ⟨h2, h1⟩)
    have he := bool_edge_le h_a1c1
    subst hb1 hb2 hz hx0; simp; omega
  | false =>
    cases a1 with
    | true =>
      have hb0 : b0 = false := by cases b0 <;> simp_all
      have hb2 : b2 = false := by cases b2 <;> simp_all
      have hc1 : c1 = false := by cases c1 <;> simp_all
      have hz : z = false := by cases z <;> simp_all
      have e1 := bool_edge_le h_a2b1; have e2 := bool_edge_le h_x0c2; have e3 := bool_edge_le h_qy
      subst hb0 hb2 hc1 hz; simp; omega
    | false =>
      cases a2 with
      | true =>
        have hb0 : b0 = false := by cases b0 <;> simp_all
        have hb1 : b1 = false := by cases b1 <;> simp_all
        have hc2 : c2 = false := by cases c2 <;> simp_all
        have hz : z = false := by cases z <;> simp_all
        have e1 := bool_edge_le h_x0c1; have e2 := bool_edge_le h_qy; have h5 := hle b2
        subst hb0 hb1 hc2 hz; simp; omega
      | false =>
        have hc5 := bool_c5_le (fun ⟨h1, h2⟩ => h_qb0 ⟨h2, h1⟩) h_qb2 h_b2c2
          (fun ⟨h1, h2⟩ => h_x0c2 ⟨h2, h1⟩) h_x0b0
        have e1 := bool_edge_le h_b1c1; have e2 := bool_edge_le h_zy
        simp; omega

lemma graph_N_step {V : Type} [Fintype V]
    (G : SimpleGraph V) (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b c : Fin 3 → V)
    (hab : ∀ i j : Fin 3, i ≠ j → G.Adj (a i) (b j))
    (hac : ∀ i : Fin 3, G.Adj (a i) (c i))
    (hbc : ∀ i : Fin 3, G.Adj (b i) (c i))
    (x0 : V) (hx0 : G.Adj x0 (a 0) ∧ G.Adj x0 (b 0) ∧ G.Adj x0 (c 1) ∧ G.Adj x0 (c 2))
    (hnc : ¬ G.Adj (c 0) (c 2)) :
    ∃ w : V, G.Adj w (a 1) ∧ G.Adj w (b 1) ∧ G.Adj w (c 0) ∧ G.Adj w (c 2) := by
  classical
  have hc02_ne : c 0 ≠ c 2 := by
    intro heq
    have h1 : G.Adj (a 0) (c 2) := by rw [← heq]; exact hac 0
    exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf h1.symm (hbc 2).symm (hab 0 2 (by decide))
  obtain ⟨y, hyc0, hyc2⟩ := hmax (c 0) (c 2) hc02_ne hnc
  -- Step 1: D_3 on (a0, a1, a2, b0, b1, b2, c0, c2, y)
  let xs1 : Fin 9 → V := ![a 0, a 1, a 2, b 0, b 1, b 2, c 0, c 2, y]
  obtain ⟨z0, f1, hf1, hsum1, hind1⟩ := prop_D_bool G hcf hmin 3 (by omega) xs1
  have hsum1' : 4 ≤ (f1 0).toNat + (f1 1).toNat + (f1 2).toNat + (f1 3).toNat +
      (f1 4).toNat + (f1 5).toNat + (f1 6).toNat + (f1 7).toNat + (f1 8).toNat := by
    rw [fin9_sum (fun k => (f1 k).toNat)] at hsum1; exact hsum1
  have hcases1 := graph_N_9_indep (f1 0) (f1 1) (f1 2) (f1 3) (f1 4) (f1 5) (f1 6) (f1 7) (f1 8)
    (hind1 0 4 (hab 0 1 (by decide))) (hind1 0 5 (hab 0 2 (by decide)))
    (hind1 1 3 (hab 1 0 (by decide))) (hind1 1 5 (hab 1 2 (by decide)))
    (hind1 2 3 (hab 2 0 (by decide))) (hind1 2 4 (hab 2 1 (by decide)))
    (hind1 0 6 (hac 0)) (hind1 3 6 (hbc 0))
    (hind1 2 7 (hac 2)) (hind1 5 7 (hbc 2))
    (hind1 8 6 hyc0.symm) (hind1 8 7 hyc2.symm) hsum1'
  rcases hcases1 with ⟨h1, h2, h3, h4⟩ | hside
  · exact ⟨z0, ((hf1 1).mp h1).symm, ((hf1 4).mp h2).symm,
      ((hf1 6).mp h3).symm, ((hf1 7).mp h4).symm⟩
  -- Helper given z ~ {a' 0, a' 1, a' 2, y} (wlog by a <-> b symmetry!)
  have finish : ∀ (a' b' : Fin 3 → V) (z : V),
      (∀ i j : Fin 3, i ≠ j → G.Adj (a' i) (b' j)) →
      (∀ i : Fin 3, G.Adj (a' i) (c i)) →
      (∀ i : Fin 3, G.Adj (b' i) (c i)) →
      (G.Adj x0 (a' 0) ∧ G.Adj x0 (b' 0) ∧ G.Adj x0 (c 1) ∧ G.Adj x0 (c 2)) →
      (G.Adj z (a' 0) ∧ G.Adj z (a' 1) ∧ G.Adj z (a' 2) ∧ G.Adj z y) →
      ∃ w : V, G.Adj w (a' 1) ∧ G.Adj w (b' 1) ∧ G.Adj w (c 0) ∧ G.Adj w (c 2) := by
    intro a' b' z hab' hac' hbc' hx0' hz
    let xs2 : Fin 9 → V := ![b' 2, a' 1, b' 0, a' 2, c 2, y, c 0, c 1, b' 1]
    obtain ⟨q, f2, hf2, hsum2, hind2⟩ := prop_D_bool G hcf hmin 3 (by omega) xs2
    have hsum2' : 4 ≤ (f2 0).toNat + (f2 1).toNat + (f2 2).toNat + (f2 3).toNat +
        (f2 4).toNat + (f2 5).toNat + (f2 6).toNat + (f2 7).toNat + (f2 8).toNat := by
      rw [fin9_sum (fun k => (f2 k).toNat)] at hsum2; exact hsum2
    have hcases2 := graph_N_pentagon_indep
      (f2 0) (f2 1) (f2 2) (f2 3) (f2 4) (f2 5) (f2 6) (f2 7) (f2 8)
      (hind2 0 1 (hab' 1 2 (by decide)).symm)
      (hind2 1 2 (hab' 1 0 (by decide)))
      (hind2 2 3 (hab' 2 0 (by decide)).symm)
      (hind2 3 4 (hac' 2))
      (hind2 4 0 (hbc' 2).symm)
      (hind2 5 6 hyc0.symm)
      (hind2 7 8 (hbc' 1).symm)
      (hind2 5 4 hyc2.symm)
      (hind2 6 2 (hbc' 0).symm)
      (hind2 8 3 (hab' 2 1 (by decide)).symm)
      (hind2 7 1 (hac' 1).symm) hsum2'
    rcases hcases2 with ⟨h1, h2, h3, h4⟩ | ⟨hb2, hb0, hyq⟩ | ⟨hb2, ha2, hc1⟩
    · exact ⟨q, ((hf2 1).mp h1).symm, ((hf2 8).mp h2).symm,
        ((hf2 6).mp h3).symm, ((hf2 4).mp h4).symm⟩
    · -- Case B: q ~ b' 2, b' 0, y => D_4 on 12 vertices (drop c 0, add q) contradicts graph_N_12_caseB
      exfalso
      have hqb2 : G.Adj q (b' 2) := ((hf2 0).mp hb2).symm
      have hqb0 : G.Adj q (b' 0) := ((hf2 2).mp hb0).symm
      have hqy : G.Adj q y := ((hf2 5).mp hyq).symm
      let xs3 : Fin 12 → V := ![a' 0, a' 1, a' 2, b' 0, b' 1, b' 2, c 1, c 2, y, z, x0, q]
      obtain ⟨_, f3, _, hsum3, hind3⟩ := prop_D_bool G hcf hmin 4 (by omega) xs3
      have hsum3' : 5 ≤ (f3 0).toNat + (f3 1).toNat + (f3 2).toNat + (f3 3).toNat +
          (f3 4).toNat + (f3 5).toNat + (f3 6).toNat + (f3 7).toNat +
          (f3 8).toNat + (f3 9).toNat + (f3 10).toNat + (f3 11).toNat := by
        rw [fin12_sum (fun k => (f3 k).toNat)] at hsum3; exact hsum3
      have hle := graph_N_12_caseB
        (f3 0) (f3 1) (f3 2) (f3 3) (f3 4) (f3 5) (f3 6) (f3 7) (f3 8) (f3 9) (f3 10) (f3 11)
        (hind3 0 4 (hab' 0 1 (by decide))) (hind3 0 5 (hab' 0 2 (by decide)))
        (hind3 1 3 (hab' 1 0 (by decide))) (hind3 1 5 (hab' 1 2 (by decide)))
        (hind3 2 3 (hab' 2 0 (by decide))) (hind3 2 4 (hab' 2 1 (by decide)))
        (hind3 1 6 (hac' 1)) (hind3 4 6 (hbc' 1))
        (hind3 2 7 (hac' 2)) (hind3 5 7 (hbc' 2))
        (hind3 8 7 hyc2.symm) (hind3 9 0 hz.1)
        (hind3 9 1 hz.2.1) (hind3 9 2 hz.2.2.1)
        (hind3 9 8 hz.2.2.2) (hind3 10 0 hx0'.1)
        (hind3 10 3 hx0'.2.1) (hind3 10 6 hx0'.2.2.1)
        (hind3 10 7 hx0'.2.2.2) (hind3 11 5 hqb2)
        (hind3 11 3 hqb0) (hind3 11 8 hqy)
      omega
    · -- Case A: q ~ b' 2, a' 2, c 1 => D_4 on 12 vertices (drop b' 1, add q) contradicts graph_N_12_caseA
      exfalso
      have hqb2 : G.Adj q (b' 2) := ((hf2 0).mp hb2).symm
      have hqa2 : G.Adj q (a' 2) := ((hf2 3).mp ha2).symm
      have hqc1 : G.Adj q (c 1) := ((hf2 7).mp hc1).symm
      let xs3 : Fin 12 → V := ![a' 0, a' 1, a' 2, b' 0, b' 2, c 0, c 1, c 2, y, z, x0, q]
      obtain ⟨_, f3, _, hsum3, hind3⟩ := prop_D_bool G hcf hmin 4 (by omega) xs3
      have hsum3' : 5 ≤ (f3 0).toNat + (f3 1).toNat + (f3 2).toNat + (f3 3).toNat +
          (f3 4).toNat + (f3 5).toNat + (f3 6).toNat + (f3 7).toNat +
          (f3 8).toNat + (f3 9).toNat + (f3 10).toNat + (f3 11).toNat := by
        rw [fin12_sum (fun k => (f3 k).toNat)] at hsum3; exact hsum3
      have hle := graph_N_12_caseA
        (f3 0) (f3 1) (f3 2) (f3 3) (f3 4) (f3 5) (f3 6) (f3 7) (f3 8) (f3 9) (f3 10) (f3 11)
        (hind3 0 4 (hab' 0 2 (by decide))) (hind3 1 3 (hab' 1 0 (by decide)))
        (hind3 1 4 (hab' 1 2 (by decide))) (hind3 2 3 (hab' 2 0 (by decide)))
        (hind3 0 5 (hac' 0)) (hind3 3 5 (hbc' 0))
        (hind3 1 6 (hac' 1)) (hind3 2 7 (hac' 2))
        (hind3 4 7 (hbc' 2)) (hind3 8 5 hyc0.symm)
        (hind3 8 7 hyc2.symm) (hind3 9 0 hz.1)
        (hind3 9 1 hz.2.1) (hind3 9 2 hz.2.2.1)
        (hind3 9 8 hz.2.2.2) (hind3 10 0 hx0'.1)
        (hind3 10 3 hx0'.2.1) (hind3 10 6 hx0'.2.2.1)
        (hind3 10 7 hx0'.2.2.2) (hind3 11 2 hqa2)
        (hind3 11 6 hqc1) (hind3 11 4 hqb2)
      omega
  rcases hside with ⟨h0, h1, h2, hy⟩ | ⟨h0, h1, h2, hy⟩
  · exact finish a b z0 hab hac hbc hx0
      ⟨((hf1 0).mp h0).symm, ((hf1 1).mp h1).symm, ((hf1 2).mp h2).symm, ((hf1 8).mp hy).symm⟩
  · obtain ⟨w, hwb, hwa, hc0, hc2⟩ := finish b a z0
      (fun i j hij => (hab j i hij.symm).symm) hbc hac
      ⟨hx0.2.1, hx0.1, hx0.2.2.1, hx0.2.2.2⟩
      ⟨((hf1 3).mp h0).symm, ((hf1 4).mp h1).symm, ((hf1 5).mp h2).symm, ((hf1 8).mp hy).symm⟩
    exact ⟨w, hwa, hwb, hc0, hc2⟩

lemma graph_N_lemma {V : Type} [Fintype V]
    (G : SimpleGraph V) (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b c : Fin 3 → V)
    (hab : ∀ i j : Fin 3, i ≠ j → G.Adj (a i) (b j))
    (hac : ∀ i : Fin 3, G.Adj (a i) (c i))
    (hbc : ∀ i : Fin 3, G.Adj (b i) (c i)) :
    ∀ i : Fin 3, G.Adj (c (i + 1)) (c (i + 2)) ∨
      ∃ w : V, G.Adj w (a i) ∧ G.Adj w (b i) ∧ G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 2)) := by
  classical
  -- First, D_3 on N gives some k0 with a common neighbor x0 of {a k0, b k0, c (k0+1), c (k0+2)}
  let xs : Fin 9 → V := ![a 0, a 1, a 2, b 0, b 1, b 2, c 0, c 1, c 2]
  obtain ⟨x0, f, hf, hsum, hind⟩ := prop_D_bool G hcf hmin 3 (by omega) xs
  let fa : Fin 3 → Bool := fun r => f ⟨r.val, by omega⟩
  let fb : Fin 3 → Bool := fun r => f ⟨r.val + 3, by omega⟩
  let fc : Fin 3 → Bool := fun r => f ⟨r.val + 6, by omega⟩
  have hsum' : 4 ≤ ∑ r : Fin 3, (fa r).toNat + ∑ r : Fin 3, (fb r).toNat +
      ∑ r : Fin 3, (fc r).toNat := by
    have h9 : ∑ k : Fin 9, (f k).toNat =
        ∑ r : Fin 3, (fa r).toNat + ∑ r : Fin 3, (fb r).toNat + ∑ r : Fin 3, (fc r).toNat := by
      rw [fin9_sum (fun x => (f x).toNat)]
      simp only [Fin.sum_univ_three, fa, fb, fc]
      change (f 0).toNat + (f 1).toNat + (f 2).toNat + (f 3).toNat + (f 4).toNat +
        (f 5).toNat + (f 6).toNat + (f 7).toNat + (f 8).toNat =
        ((f 0).toNat + (f 1).toNat + (f 2).toNat) +
        ((f 3).toNat + (f 4).toNat + (f 5).toNat) +
        ((f 6).toNat + (f 7).toNat + (f 8).toNat)
      omega
    rw [← h9]; exact hsum
  obtain ⟨k0, ha0, hb0, hc0⟩ := cube_9_indep fa fb fc
    (fun r₁ r₂ hr => by
      have h := hind ⟨r₁.val, by omega⟩ ⟨r₂.val + 3, by omega⟩
      fin_cases r₁ <;> fin_cases r₂ <;> first | exact absurd rfl hr | exact h (hab _ _ hr))
    (fun r => by
      have h := hind ⟨r.val, by omega⟩ ⟨r.val + 6, by omega⟩
      fin_cases r <;> exact h (hac _))
    (fun r => by
      have h := hind ⟨r.val + 3, by omega⟩ ⟨r.val + 6, by omega⟩
      fin_cases r <;> exact h (hbc _))
    hsum'
  have hx0 : G.Adj x0 (a k0) ∧ G.Adj x0 (b k0) ∧
      G.Adj x0 (c (k0 + 1)) ∧ G.Adj x0 (c (k0 + 2)) := by
    have h1 : G.Adj (a k0) x0 := by
      have := (hf ⟨k0.val, by omega⟩).mp ha0
      fin_cases k0 <;> simpa [xs] using this
    have h2 : G.Adj (b k0) x0 := by
      have := (hf ⟨k0.val + 3, by omega⟩).mp hb0
      fin_cases k0 <;> simpa [xs] using this
    have h3 : G.Adj (c (k0 + 1)) x0 := by
      have hne : k0 + 1 ≠ k0 := by fin_cases k0 <;> decide
      have := (hf ⟨(k0 + 1).val + 6, by omega⟩).mp (hc0 (k0 + 1) hne)
      fin_cases k0 <;> simpa [xs] using this
    have h4 : G.Adj (c (k0 + 2)) x0 := by
      have hne : k0 + 2 ≠ k0 := by fin_cases k0 <;> decide
      have := (hf ⟨(k0 + 2).val + 6, by omega⟩).mp (hc0 (k0 + 2) hne)
      fin_cases k0 <;> simpa [xs] using this
    exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩
  intro i
  by_cases hik : i = k0
  · subst hik; exact Or.inr ⟨x0, hx0⟩
  by_cases hadj : G.Adj (c (i + 1)) (c (i + 2))
  · exact Or.inl hadj
  right
  -- Build permutation p : Fin 3 → Fin 3 with p 0 = k0, p 1 = i, p 2 = third index
  by_cases hi1 : i = k0 + 1
  · subst hi1
    have hstep := graph_N_step G hcf hmax hmin
      (fun r => a (k0 + r)) (fun r => b (k0 + r)) (fun r => c (k0 + r))
      (fun r₁ r₂ hr => hab _ _ (fun heq => hr (add_left_cancel heq)))
      (fun r => hac _) (fun r => hbc _) x0
      (by simpa using hx0)
      (by
        have h02 : (k0 + 0 : Fin 3) = k0 + 1 + 2 := by fin_cases k0 <;> rfl
        have h21 : (k0 + 2 : Fin 3) = k0 + 1 + 1 := by fin_cases k0 <;> rfl
        rw [h02, h21]; exact fun h => hadj h.symm)
    obtain ⟨w, h1, h2, h3, h4⟩ := hstep
    have h02 : (k0 + 0 : Fin 3) = k0 + 1 + 2 := by fin_cases k0 <;> rfl
    have h21 : (k0 + 2 : Fin 3) = k0 + 1 + 1 := by fin_cases k0 <;> rfl
    rw [h02] at h3; rw [h21] at h4
    exact ⟨w, h1, h2, h4, h3⟩
  · have hi2 : i = k0 + 2 := by fin_cases k0 <;> fin_cases i <;> simp_all
    subst hi2
    have hstep := graph_N_step G hcf hmax hmin
      (fun r => a (k0 - r)) (fun r => b (k0 - r)) (fun r => c (k0 - r))
      (fun r₁ r₂ hr => hab _ _ (fun heq => hr (sub_right_inj.mp heq)))
      (fun r => hac _) (fun r => hbc _) x0
      (by
        have h1 : (k0 - 1 : Fin 3) = k0 + 2 := by fin_cases k0 <;> rfl
        have h2 : (k0 - 2 : Fin 3) = k0 + 1 := by fin_cases k0 <;> rfl
        simpa [h1, h2] using ⟨hx0.1, hx0.2.1, hx0.2.2.2, hx0.2.2.1⟩)
      (by
        have h01 : (k0 - 0 : Fin 3) = k0 + 2 + 1 := by fin_cases k0 <;> rfl
        have h22 : (k0 - 2 : Fin 3) = k0 + 2 + 2 := by fin_cases k0 <;> rfl
        rw [h01, h22]; exact hadj)
    obtain ⟨w, h1, h2, h3, h4⟩ := hstep
    have h1eq : (k0 - 1 : Fin 3) = k0 + 2 := by fin_cases k0 <;> rfl
    have h01 : (k0 - 0 : Fin 3) = k0 + 2 + 1 := by fin_cases k0 <;> rfl
    have h22 : (k0 - 2 : Fin 3) = k0 + 2 + 2 := by fin_cases k0 <;> rfl
    rw [h1eq] at h1 h2; rw [h01] at h3; rw [h22] at h4
    exact ⟨w, h1, h2, h3, h4⟩

/- ### Part 4: Beautiful Lemma (Lemma 4.3) & Grötzsch Center Twin (Lemma 4.4) -/

lemma beautiful_12_step1 (a0 a1 a2 a4 b0 b1 b2 b3 b4 c q z : Bool)
    (hca0 : ¬ (c = true ∧ a0 = true)) (hca1 : ¬ (c = true ∧ a1 = true))
    (hca2 : ¬ (c = true ∧ a2 = true)) (hca4 : ¬ (c = true ∧ a4 = true))
    (ha0b2 : ¬ (a0 = true ∧ b2 = true)) (ha0b3 : ¬ (a0 = true ∧ b3 = true))
    (ha1b3 : ¬ (a1 = true ∧ b3 = true)) (ha1b4 : ¬ (a1 = true ∧ b4 = true))
    (ha2b4 : ¬ (a2 = true ∧ b4 = true)) (ha2b0 : ¬ (a2 = true ∧ b0 = true))
    (ha4b1 : ¬ (a4 = true ∧ b1 = true)) (ha4b2 : ¬ (a4 = true ∧ b2 = true))
    (hb0b2 : ¬ (b0 = true ∧ b2 = true)) (hb1b3 : ¬ (b1 = true ∧ b3 = true))
    (hb2b4 : ¬ (b2 = true ∧ b4 = true)) (hb3b0 : ¬ (b3 = true ∧ b0 = true))
    (hb4b1 : ¬ (b4 = true ∧ b1 = true))
    (hqa0 : ¬ (q = true ∧ a0 = true)) (hqa2 : ¬ (q = true ∧ a2 = true))
    (hza1 : ¬ (z = true ∧ a1 = true)) (hzq : ¬ (z = true ∧ q = true))
    (hsum : 5 ≤ a0.toNat + a1.toNat + a2.toNat + a4.toNat + b0.toNat + b1.toNat +
      b2.toNat + b3.toNat + b4.toNat + c.toNat + q.toNat + z.toNat) :
    a0 = true ∧ a4 = true ∧ b0 = true ∧ b4 = true ∧ z = true := by
  have hle : ∀ x : Bool, x.toNat ≤ 1 := fun x => by cases x <;> decide
  have hc5_b := bool_c5_le hb0b2 hb2b4 hb4b1 hb1b3 hb3b0
  have ha0 : a0 = true := by
    cases a0; swap; rfl
    exfalso
    cases a1 with
    | true =>
      have hc : c = false := by cases c <;> simp_all
      have hb3 : b3 = false := by cases b3 <;> simp_all
      have hb4 : b4 = false := by cases b4 <;> simp_all
      have hz : z = false := by cases z <;> simp_all
      have e1 := bool_edge_le hqa2; have e2 := bool_edge_le ha4b1; have e3 := bool_edge_le hb0b2
      subst hc hb3 hb4 hz; simp at hsum; omega
    | false =>
      cases a2 with
      | true =>
        have hc : c = false := by cases c <;> simp_all
        have hb0 : b0 = false := by cases b0 <;> simp_all
        have hb4 : b4 = false := by cases b4 <;> simp_all
        have hq : q = false := by cases q <;> simp_all
        have e1 := bool_edge_le ha4b2; have e2 := bool_edge_le hb1b3; have hz1 := hle z
        subst hc hb0 hb4 hq; simp at hsum; omega
      | false =>
        have e1 := bool_edge_le hca4; have e2 := bool_edge_le hzq
        simp at hsum; omega
  have ha4 : a4 = true := by
    cases a4; swap; rfl
    exfalso
    have hb2 : b2 = false := by cases b2 <;> simp_all
    have hb3 : b3 = false := by cases b3 <;> simp_all
    have hc : c = false := by cases c <;> simp_all
    have hq : q = false := by cases q <;> simp_all
    have e1 := bool_edge_le hza1; have e2 := bool_edge_le ha2b0; have e3 := bool_edge_le hb4b1
    subst ha0 hb2 hb3 hc hq; simp at hsum; omega
  have hb0 : b0 = true := by
    cases b0; swap; rfl
    exfalso
    have hb2 : b2 = false := by cases b2 <;> simp_all
    have hb3 : b3 = false := by cases b3 <;> simp_all
    have hc : c = false := by cases c <;> simp_all
    have hq : q = false := by cases q <;> simp_all
    have e1 := bool_edge_le hza1; have e2 := bool_edge_le ha2b4; have e3 := bool_edge_le ha4b1
    subst ha0 hb2 hb3 hc hq; simp at hsum; omega
  have hb4 : b4 = true := by
    cases b4; swap; rfl
    exfalso
    have hb2 : b2 = false := by cases b2 <;> simp_all
    have hb3 : b3 = false := by cases b3 <;> simp_all
    have hc : c = false := by cases c <;> simp_all
    have hq : q = false := by cases q <;> simp_all
    have e1 := bool_edge_le hza1; have e2 := bool_edge_le ha2b0; have e3 := bool_edge_le ha4b1
    subst ha0 hb2 hb3 hc hq; simp at hsum; omega
  have hz : z = true := by
    cases z; swap; rfl
    exfalso
    have hb2 : b2 = false := by cases b2 <;> simp_all
    have hb3 : b3 = false := by cases b3 <;> simp_all
    have hc : c = false := by cases c <;> simp_all
    have hq : q = false := by cases q <;> simp_all
    have e1 := bool_edge_le ha1b4; have e2 := bool_edge_le ha2b0; have e3 := bool_edge_le ha4b1
    subst ha0 hb2 hb3 hc hq; simp at hsum; omega
  exact ⟨ha0, ha4, hb0, hb4, hz⟩

lemma beautiful_12_step2 (a0 a1 a2 a3 b0 b1 b3 b4 c q z b2p : Bool)
    (hca0 : ¬ (c = true ∧ a0 = true)) (hca1 : ¬ (c = true ∧ a1 = true))
    (hca2 : ¬ (c = true ∧ a2 = true)) (hca3 : ¬ (c = true ∧ a3 = true))
    (ha0b3 : ¬ (a0 = true ∧ b3 = true)) (ha1b3 : ¬ (a1 = true ∧ b3 = true))
    (ha1b4 : ¬ (a1 = true ∧ b4 = true)) (ha2b4 : ¬ (a2 = true ∧ b4 = true))
    (ha2b0 : ¬ (a2 = true ∧ b0 = true)) (ha3b0 : ¬ (a3 = true ∧ b0 = true))
    (ha3b1 : ¬ (a3 = true ∧ b1 = true))
    (hb1b3 : ¬ (b1 = true ∧ b3 = true)) (hb3b0 : ¬ (b3 = true ∧ b0 = true))
    (hb4b1 : ¬ (b4 = true ∧ b1 = true))
    (hqa0 : ¬ (q = true ∧ a0 = true)) (hqa2 : ¬ (q = true ∧ a2 = true))
    (hza1 : ¬ (z = true ∧ a1 = true)) (hzq : ¬ (z = true ∧ q = true))
    (hb2pa0 : ¬ (b2p = true ∧ a0 = true)) (hb2pb0 : ¬ (b2p = true ∧ b0 = true))
    (hb2pb4 : ¬ (b2p = true ∧ b4 = true)) (hb2pz : ¬ (b2p = true ∧ z = true)) :
    a0.toNat + a1.toNat + a2.toNat + a3.toNat + b0.toNat + b1.toNat +
    b3.toNat + b4.toNat + c.toNat + q.toNat + z.toNat + b2p.toNat ≤ 4 := by
  have hle : ∀ x : Bool, x.toNat ≤ 1 := fun x => by cases x <;> decide
  cases a0 with
  | true =>
    have hb3 : b3 = false := by cases b3 <;> simp_all
    have hc : c = false := by cases c <;> simp_all
    have hq : q = false := by cases q <;> simp_all
    have hb2p : b2p = false := by cases b2p <;> simp_all
    have hc5 := bool_c5_le ha2b0 (fun ⟨h1, h2⟩ => ha3b0 ⟨h2, h1⟩) ha3b1
      (fun ⟨h1, h2⟩ => hb4b1 ⟨h2, h1⟩) (fun ⟨h1, h2⟩ => ha2b4 ⟨h2, h1⟩)
    have he := bool_edge_le hza1
    subst hb3 hc hq hb2p; simp; omega
  | false =>
    cases a1 with
    | true =>
      have hb3 : b3 = false := by cases b3 <;> simp_all
      have hb4 : b4 = false := by cases b4 <;> simp_all
      have hc : c = false := by cases c <;> simp_all
      have hz : z = false := by cases z <;> simp_all
      have e1 := bool_edge_le hqa2; have e2 := bool_edge_le ha3b1; have e3 := bool_edge_le hb2pb0
      subst hb3 hb4 hc hz; simp; omega
    | false =>
      cases a2 with
      | true =>
        have hb0 : b0 = false := by cases b0 <;> simp_all
        have hb4 : b4 = false := by cases b4 <;> simp_all
        have hc : c = false := by cases c <;> simp_all
        have hq : q = false := by cases q <;> simp_all
        have e1 := bool_edge_le hb1b3; have e2 := bool_edge_le hb2pz; have h3 := hle a3
        subst hb0 hb4 hc hq; simp; omega
      | false =>
        have hc5 := bool_c5_le (fun ⟨h1, h2⟩ => hb2pb0 ⟨h2, h1⟩) hb2pb4 hb4b1 hb1b3 hb3b0
        have e1 := bool_edge_le hca3; have e2 := bool_edge_le hzq
        simp; omega

-- Beautiful Lemma (Lemma 4.3): in a Grötzsch subgraph (a, b, c) where c ~ a_k,
-- a_k ~ b_{k+2}, a_k ~ b_{k+3}, b_k ~ b_{k+2}, if q ~ a_{k-1} and q ~ a_{k+1}, then q ~ a_k.
lemma beautiful_lemma {V : Type} [Fintype V]
    (G : SimpleGraph V) (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b : Fin 5 → V) (c : V)
    (hca : ∀ k : Fin 5, G.Adj c (a k))
    (hab2 : ∀ k : Fin 5, G.Adj (a k) (b (k + 2)))
    (hab3 : ∀ k : Fin 5, G.Adj (a k) (b (k + 3)))
    (hbb : ∀ k : Fin 5, G.Adj (b k) (b (k + 2)))
    (k : Fin 5) (q : V)
    (hq1 : G.Adj q (a (k - 1))) (hq2 : G.Adj q (a (k + 1))) :
    G.Adj q (a k) := by
  classical
  -- Shift indices by k - 1 so that k becomes 1, k - 1 becomes 0, k + 1 becomes 2
  let a' : Fin 5 → V := fun r => a (r + (k - 1))
  let b' : Fin 5 → V := fun r => b (r + (k - 1))
  have hca' : ∀ r : Fin 5, G.Adj c (a' r) := fun r => hca _
  have hab2' : ∀ r : Fin 5, G.Adj (a' r) (b' (r + 2)) := fun r => by
    have : r + 2 + (k - 1) = r + (k - 1) + 2 := add_right_comm r 2 (k - 1)
    simpa [a', b', this] using hab2 (r + (k - 1))
  have hab3' : ∀ r : Fin 5, G.Adj (a' r) (b' (r + 3)) := fun r => by
    have : r + 3 + (k - 1) = r + (k - 1) + 3 := add_right_comm r 3 (k - 1)
    simpa [a', b', this] using hab3 (r + (k - 1))
  have hbb' : ∀ r : Fin 5, G.Adj (b' r) (b' (r + 2)) := fun r => by
    have : r + 2 + (k - 1) = r + (k - 1) + 2 := add_right_comm r 2 (k - 1)
    simpa [b', this] using hbb (r + (k - 1))
  have hqa0 : G.Adj q (a' 0) := by simpa [a'] using hq1
  have hqa2 : G.Adj q (a' 2) := by
    have : (2 : Fin 5) + (k - 1) = k + 1 := fin5_sub1_add2 k
    simpa [a', this] using hq2
  have hgoal : G.Adj q (a' 1) → G.Adj q (a k) := by
    have : (1 : Fin 5) + (k - 1) = k := fin5_sub1_add1 k
    simp [a', this]
  apply hgoal
  by_contra hnq
  have hne : a' 1 ≠ q := by
    intro heq
    rw [← heq] at hqa0
    exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf (hca' 1) (hca' 0) hqa0
  obtain ⟨z, hza1, hzq⟩ := hmax (a' 1) q hne (fun h => hnq h.symm)
  -- Step 1: D_4 on Grotzsch - a' 3 + q + z (12 vertices)
  let xs1 : Fin 12 → V := fun x => match x.val with
    | 0 => a' 0 | 1 => a' 1 | 2 => a' 2 | 3 => a' 4
    | 4 => b' 0 | 5 => b' 1 | 6 => b' 2 | 7 => b' 3
    | 8 => b' 4 | 9 => c    | 10 => q   | _ => z
  obtain ⟨b2p, f1, hf1, hsum1, hind1⟩ := prop_D_bool G hcf hmin 4 (by omega) xs1
  have hsum1' : 5 ≤ (f1 0).toNat + (f1 1).toNat + (f1 2).toNat + (f1 3).toNat +
      (f1 4).toNat + (f1 5).toNat + (f1 6).toNat + (f1 7).toNat +
      (f1 8).toNat + (f1 9).toNat + (f1 10).toNat + (f1 11).toNat := by
    rw [fin12_sum (fun r => (f1 r).toNat)] at hsum1; exact hsum1
  have ⟨hb2p_a0, _, hb2p_b0, hb2p_b4, hb2p_z⟩ := beautiful_12_step1
    (f1 0) (f1 1) (f1 2) (f1 3) (f1 4) (f1 5) (f1 6) (f1 7) (f1 8) (f1 9) (f1 10) (f1 11)
    (hind1 9 0 (hca' 0)) (hind1 9 1 (hca' 1)) (hind1 9 2 (hca' 2)) (hind1 9 3 (hca' 4))
    (hind1 0 6 (hab2' 0)) (hind1 0 7 (hab3' 0))
    (hind1 1 7 (hab2' 1)) (hind1 1 8 (hab3' 1))
    (hind1 2 8 (hab2' 2)) (hind1 2 4 (hab3' 2))
    (hind1 3 5 (hab2' 4)) (hind1 3 6 (hab3' 4))
    (hind1 4 6 (hbb' 0)) (hind1 5 7 (hbb' 1))
    (hind1 6 8 (hbb' 2)) (hind1 7 4 (hbb' 3)) (hind1 8 5 (hbb' 4))
    (hind1 10 0 hqa0) (hind1 10 2 hqa2)
    (hind1 11 1 hza1.symm) (hind1 11 10 hzq.symm) hsum1'
  -- Step 2: D_4 on Grotzsch - b' 2 - a' 4 + q + z + b2p (12 vertices) -> contradiction!
  let xs2 : Fin 12 → V := fun x => match x.val with
    | 0 => a' 0 | 1 => a' 1 | 2 => a' 2 | 3 => a' 3
    | 4 => b' 0 | 5 => b' 1 | 6 => b' 3 | 7 => b' 4
    | 8 => c    | 9 => q    | 10 => z   | _ => b2p
  obtain ⟨_, f2, _, hsum2, hind2⟩ := prop_D_bool G hcf hmin 4 (by omega) xs2
  have hsum2' : 5 ≤ (f2 0).toNat + (f2 1).toNat + (f2 2).toNat + (f2 3).toNat +
      (f2 4).toNat + (f2 5).toNat + (f2 6).toNat + (f2 7).toNat +
      (f2 8).toNat + (f2 9).toNat + (f2 10).toNat + (f2 11).toNat := by
    rw [fin12_sum (fun r => (f2 r).toNat)] at hsum2; exact hsum2
  have hle := beautiful_12_step2
    (f2 0) (f2 1) (f2 2) (f2 3) (f2 4) (f2 5) (f2 6) (f2 7) (f2 8) (f2 9) (f2 10) (f2 11)
    (hind2 8 0 (hca' 0)) (hind2 8 1 (hca' 1)) (hind2 8 2 (hca' 2)) (hind2 8 3 (hca' 3))
    (hind2 0 6 (hab3' 0)) (hind2 1 6 (hab2' 1)) (hind2 1 7 (hab3' 1))
    (hind2 2 7 (hab2' 2)) (hind2 2 4 (hab3' 2))
    (hind2 3 4 (hab2' 3)) (hind2 3 5 (hab3' 3))
    (hind2 5 6 (hbb' 1)) (hind2 6 4 (hbb' 3)) (hind2 7 5 (hbb' 4))
    (hind2 9 0 hqa0) (hind2 9 2 hqa2)
    (hind2 10 1 hza1.symm) (hind2 10 9 hzq.symm)
    (hind2 11 0 ((hf1 0).mp hb2p_a0).symm) (hind2 11 4 ((hf1 4).mp hb2p_b0).symm)
    (hind2 11 7 ((hf1 8).mp hb2p_b4).symm) (hind2 11 10 ((hf1 11).mp hb2p_z).symm)
  omega

-- Lemma 4.4: (Υ, c a_k)-twin property holds unconditionally in D_4.
lemma grotzsch_center_twin {V : Type} [Fintype V]
    (G : SimpleGraph V) (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b : Fin 5 → V) (c : V)
    (hca : ∀ r : Fin 5, G.Adj c (a r))
    (hab2 : ∀ r : Fin 5, G.Adj (a r) (b (r + 2)))
    (hab3 : ∀ r : Fin 5, G.Adj (a r) (b (r + 3)))
    (hbb : ∀ r : Fin 5, G.Adj (b r) (b (r + 2)))
    (k : Fin 5) (c' a' : V)
    (hc' : ∀ r : Fin 5, G.Adj c' (a r))
    (ha' : G.Adj a' c ∧ G.Adj a' (b (k + 2)) ∧ G.Adj a' (b (k + 3))) :
    G.Adj c' a' := by
  let a1 : Fin 5 → V := Function.update a k a'
  have hca1 : ∀ r : Fin 5, G.Adj c (a1 r) := fun r => by
    by_cases h : r = k
    · subst h; simpa [a1] using ha'.1.symm
    · simpa [a1, h] using hca r
  have hab2_1 : ∀ r : Fin 5, G.Adj (a1 r) (b (r + 2)) := fun r => by
    by_cases h : r = k
    · subst h; simpa [a1] using ha'.2.1
    · simpa [a1, h] using hab2 r
  have hab3_1 : ∀ r : Fin 5, G.Adj (a1 r) (b (r + 3)) := fun r => by
    by_cases h : r = k
    · subst h; simpa [a1] using ha'.2.2
    · simpa [a1, h] using hab3 r
  have h1 : G.Adj c' (a1 (k - 1)) := by
    have hne : k - 1 ≠ k := by fin_cases k <;> decide
    simpa [a1, hne] using hc' (k - 1)
  have h2 : G.Adj c' (a1 (k + 1)) := by
    have hne : k + 1 ≠ k := by fin_cases k <;> decide
    simpa [a1, hne] using hc' (k + 1)
  have hres := beautiful_lemma G hcf hmax hmin a1 b c hca1 hab2_1 hab3_1 hbb k c' h1 h2
  simpa [a1] using hres

/- ### Part 5: Vega Graph Core Properties (symmetry, maximal triangle-freeness, injectivity) -/

lemma vega_adj_symm {i : ℕ} (hi : 2 ≤ i) (a b : Fin (3 * i - 1) ⊕ Fin 8) :
    (match a, b with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) →
    (match b, a with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) := by
  cases a with
  | inl p =>
    cases b with
    | inl q => exact (OMA.R_Erdos128_erdos_128_R2_H2_R2.and_adj_symm (by omega) p.isLt q.isLt).mp
    | inr t => exact id
  | inr t₁ =>
    cases b with
    | inl p => exact id
    | inr t₂ =>
      intro h
      rcases h with ⟨h1, h2, h3 | h3⟩ | h | h | h | h
      · exact Or.inl ⟨h2, h1, Or.inr h3⟩
      · exact Or.inl ⟨h2, h1, Or.inl h3⟩
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

-- Every active vertex of Υ_i^{μν} has an active neighbor.
lemma vega_has_neighbor {i : ℕ} (_hi : 2 ≤ i) (μ ν : Bool) (a : Fin (3 * i - 1) ⊕ Fin 8) :
    ∃ r : Fin (3 * i - 1) ⊕ Fin 8,
      (match r with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) ∧
      (match a, r with
        | Sum.inl p, Sum.inl q =>
            i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
            (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ =>
            (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
            (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
            (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
            (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
            (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) := by
  cases a with
  | inl p =>
    by_cases hp1 : p.val < i
    · exact ⟨Sum.inr 0, by simp, Or.inl ⟨Or.inl rfl, hp1⟩⟩
    · by_cases hp2 : p.val < 2 * i
      · exact ⟨Sum.inr 4, by simp, Or.inr (Or.inl ⟨Or.inl rfl, by omega, hp2⟩)⟩
      · exact ⟨Sum.inr 2, by simp, Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)⟩
  | inr t =>
    fin_cases t
    · exact ⟨Sum.inr 1, by simp, Or.inl (by decide)⟩
    · exact ⟨Sum.inr 0, by simp, Or.inl (by decide)⟩
    · exact ⟨Sum.inr 1, by simp, Or.inl (by decide)⟩
    · exact ⟨Sum.inr 2, by simp, Or.inl (by decide)⟩
    · exact ⟨Sum.inr 3, by simp, Or.inl (by decide)⟩
    · exact ⟨Sum.inr 4, by simp, Or.inl (by decide)⟩
    · exact ⟨Sum.inr 0, by simp, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
    · exact ⟨Sum.inr 3, by simp, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))⟩

-- Explicit common-neighbor witness for non-adjacent external vertices in Υ_i^{μν}
lemma ext_common_nbr (t₁ t₂ : Fin 8) (hne : t₁ ≠ t₂)
    (hnadj : ¬ ((t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
      (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
      (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
      (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
      (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)))) :
    (∃ t : Fin 8, t.val ≠ 7 ∧
      ((t₁.val < 6 ∧ t.val < 6 ∧ ((t₁.val + 1) % 6 = t.val ∨ (t.val + 1) % 6 = t₁.val)) ∨
       (t₁.val = 6 ∧ (t.val = 0 ∨ t.val = 4 ∨ t.val = 2 ∨ t.val = 7)) ∨
       (t.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
       (t₁.val = 7 ∧ (t.val = 3 ∨ t.val = 1 ∨ t.val = 5 ∨ t.val = 6)) ∨
       (t.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) ∧
      ((t₂.val < 6 ∧ t.val < 6 ∧ ((t₂.val + 1) % 6 = t.val ∨ (t.val + 1) % 6 = t₂.val)) ∨
       (t₂.val = 6 ∧ (t.val = 0 ∨ t.val = 4 ∨ t.val = 2 ∨ t.val = 7)) ∨
       (t.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
       (t₂.val = 7 ∧ (t.val = 3 ∨ t.val = 1 ∨ t.val = 5 ∨ t.val = 6)) ∨
       (t.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)))) ∨
    ((t₁.val = 0 ∨ t₁.val = 3) ∧ (t₂.val = 0 ∨ t₂.val = 3)) ∨
    ((t₁.val = 4 ∨ t₁.val = 1) ∧ (t₂.val = 4 ∨ t₂.val = 1)) ∨
    ((t₁.val = 2 ∨ t₁.val = 5) ∧ (t₂.val = 2 ∨ t₂.val = 5)) := by
  let eadj : Fin 8 → Fin 8 → Bool := fun a b =>
    (decide (a.val < 6) && decide (b.val < 6) && ((a.val + 1) % 6 == b.val || (b.val + 1) % 6 == a.val)) ||
    (a.val == 6 && (b.val == 0 || b.val == 4 || b.val == 2 || b.val == 7)) ||
    (b.val == 6 && (a.val == 0 || a.val == 4 || a.val == 2 || a.val == 7)) ||
    (a.val == 7 && (b.val == 3 || b.val == 1 || b.val == 5 || b.val == 6)) ||
    (b.val == 7 && (a.val == 3 || a.val == 1 || a.val == 5 || a.val == 6))
  let w : Fin 8 → Fin 8 → Fin 8 := fun a b => match a.val, b.val with
    | 0, 2 => 1 | 2, 0 => 1 | 0, 4 => 5 | 4, 0 => 5 | 2, 4 => 3 | 4, 2 => 3
    | 1, 3 => 2 | 3, 1 => 2 | 1, 5 => 0 | 5, 1 => 0 | 3, 5 => 4 | 5, 3 => 4
    | 6, 1 => 0 | 1, 6 => 0 | 6, 3 => 2 | 3, 6 => 2 | 6, 5 => 4 | 5, 6 => 4
    | 7, 0 => 1 | 0, 7 => 1 | 7, 2 => 1 | 2, 7 => 1 | 7, 4 => 3 | 4, 7 => 3
    | _, _ => 0
  have he : ∀ a b : Fin 8, eadj a b = true ↔
      ((a.val < 6 ∧ b.val < 6 ∧ ((a.val + 1) % 6 = b.val ∨ (b.val + 1) % 6 = a.val)) ∨
       (a.val = 6 ∧ (b.val = 0 ∨ b.val = 4 ∨ b.val = 2 ∨ b.val = 7)) ∨
       (b.val = 6 ∧ (a.val = 0 ∨ a.val = 4 ∨ a.val = 2 ∨ a.val = 7)) ∨
       (a.val = 7 ∧ (b.val = 3 ∨ b.val = 1 ∨ b.val = 5 ∨ b.val = 6)) ∨
       (b.val = 7 ∧ (a.val = 3 ∨ a.val = 1 ∨ a.val = 5 ∨ a.val = 6))) := by
    intro a b; simp only [eadj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, or_assoc, and_assoc]
  have hok : ∀ a b : Fin 8,
      (a == b || eadj a b ||
        ((w a b).val != 7 && eadj a (w a b) && eadj b (w a b)) ||
        ((a.val == 0 || a.val == 3) && (b.val == 0 || b.val == 3)) ||
        ((a.val == 4 || a.val == 1) && (b.val == 4 || b.val == 1)) ||
        ((a.val == 2 || a.val == 5) && (b.val == 2 || b.val == 5))) = true := by decide
  have h := hok t₁ t₂
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
  rcases h with (((((h | h) | ⟨⟨h1, h2⟩, h3⟩) | h) | h) | h)
  · exact absurd h hne
  · exact absurd ((he t₁ t₂).mp h) hnadj
  · exact Or.inl ⟨w t₁ t₂, h1, (he t₁ (w t₁ t₂)).mp h2, (he t₂ (w t₁ t₂)).mp h3⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

-- Every Vega graph Υ_i^{μν} is maximal triangle-free: every distinct non-adjacent active pair
-- has an active common neighbor.
lemma vega_maximal_tf {i : ℕ} (hi : 2 ≤ i) (μ ν : Bool)
    (a b : Fin (3 * i - 1) ⊕ Fin 8)
    (ha : (fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) a)
    (hb : (fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) b)
    (hne : a ≠ b)
    (hnadj : ¬ ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b)) :
    ∃ r : Fin (3 * i - 1) ⊕ Fin 8,
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) r) ∧
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q =>
            i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
            (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ =>
            (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
            (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
            (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
            (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
            (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a r) ∧
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q =>
            i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
            (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ =>
            (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
            (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
            (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
            (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
            (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) b r) := by
  have _ := ha; have _ := hb
  cases a with
  | inl p =>
    cases b with
    | inl q =>
      -- Same color -> external hexagon vertex
      by_cases hR : p.val < i ∧ q.val < i
      · exact ⟨Sum.inr 0, by simp, Or.inl ⟨Or.inl rfl, hR.1⟩, Or.inl ⟨Or.inl rfl, hR.2⟩⟩
      by_cases hG : (i ≤ p.val ∧ p.val < 2 * i) ∧ (i ≤ q.val ∧ q.val < 2 * i)
      · exact ⟨Sum.inr 4, by simp, Or.inr (Or.inl ⟨Or.inl rfl, hG.1⟩), Or.inr (Or.inl ⟨Or.inl rfl, hG.2⟩)⟩
      by_cases hB : 2 * i ≤ p.val ∧ 2 * i ≤ q.val
      · exact ⟨Sum.inr 2, by simp, Or.inr (Or.inr ⟨Or.inl rfl, hB.1⟩), Or.inr (Or.inr ⟨Or.inl rfl, hB.2⟩)⟩
      -- Different colors, non-adjacent in Γ_i: pick r = (hi_v + i) % (3i - 1)
      have hpq_ne : p.val ≠ q.val := fun h => hne (congrArg Sum.inl (Fin.ext h))
      have hm_pos : 0 < 3 * i - 1 := by omega
      let d := (q.val + (3 * i - 1) - p.val) % (3 * i - 1)
      have hd_ne0 : d ≠ 0 := by
        intro hd0; dsimp only [d] at hd0
        have hp := p.isLt; have hq := q.isLt
        by_cases hle : p.val ≤ q.val
        · have : q.val + (3 * i - 1) - p.val = (q.val - p.val) + (3 * i - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hd0; omega
        · have : (q.val + (3 * i - 1) - p.val) < 3 * i - 1 := by omega
          rw [Nat.mod_eq_of_lt this] at hd0; omega
      have hd_lt : d < 3 * i - 1 := Nat.mod_lt _ hm_pos
      have hd_cases : d < i ∨ 2 * i ≤ d := by
        by_contra h; push Not at h; exact hnadj ⟨h.1, by omega⟩
      rcases hd_cases with hd1 | hd2
      · -- 1 ≤ d < i: let r = (q + i) % (3i - 1)
        let rv := (q.val + i) % (3 * i - 1)
        have hrv_lt : rv < 3 * i - 1 := Nat.mod_lt _ hm_pos
        have hrv_ne : rv ≠ 2 * i - 1 := by
          intro hrv; dsimp only [rv] at hrv
          have hq := q.isLt; have hp := p.isLt
          have hqeq : q.val = i - 1 := by
            by_cases hq2 : q.val + i < 3 * i - 1
            · rw [Nat.mod_eq_of_lt hq2] at hrv; omega
            · have : q.val + i = (q.val + i - (3 * i - 1)) + (3 * i - 1) := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hrv; omega
          have hplt : p.val < i := by
            by_cases hle : p.val ≤ q.val
            · omega
            · have : q.val + (3 * i - 1) - p.val < 3 * i - 1 := by omega
              have hd_eq : d = q.val + (3 * i - 1) - p.val := Nat.mod_eq_of_lt this
              omega
          exact hR ⟨hplt, by omega⟩
        refine ⟨Sum.inl ⟨rv, hrv_lt⟩, fun _ => hrv_ne, ?_, ?_⟩
        · dsimp only
          have h1 : (rv + (3 * i - 1) - p.val) % (3 * i - 1) = d + i := by
            have hq := q.isLt; have hp := p.isLt
            have hmod : (rv + (3 * i - 1) - p.val) % (3 * i - 1) =
                ((q.val + (3 * i - 1) - p.val) + i) % (3 * i - 1) := by
              by_cases hqi : q.val + i < 3 * i - 1
              · have hrv_e : rv = q.val + i := Nat.mod_eq_of_lt hqi
                rw [hrv_e]; congr 1; omega
              · have hrv_e : rv = q.val + i - (3 * i - 1) := by
                  have : q.val + i = (q.val + i - (3 * i - 1)) + (3 * i - 1) := by omega
                  dsimp only [rv]; rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
                rw [hrv_e]
                have heq : q.val + (3 * i - 1) - p.val + i =
                    (q.val + i - (3 * i - 1) + (3 * i - 1) - p.val) + (3 * i - 1) := by omega
                rw [heq, Nat.add_mod_right]
            rw [hmod, Nat.add_mod, show (q.val + (3 * i - 1) - p.val) % (3 * i - 1) = d from rfl,
                Nat.mod_eq_of_lt (by omega : i < 3 * i - 1), Nat.mod_eq_of_lt (by omega)]
          rw [h1]; omega
        · dsimp only
          have h2 : (rv + (3 * i - 1) - q.val) % (3 * i - 1) = i := by
            have hq := q.isLt
            by_cases hqi : q.val + i < 3 * i - 1
            · have hrv_e : rv = q.val + i := Nat.mod_eq_of_lt hqi
              rw [hrv_e, show q.val + i + (3 * i - 1) - q.val = i + (3 * i - 1) by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            · have hrv_e : rv = q.val + i - (3 * i - 1) := by
                have : q.val + i = (q.val + i - (3 * i - 1)) + (3 * i - 1) := by omega
                dsimp only [rv]; rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
              rw [hrv_e, show q.val + i - (3 * i - 1) + (3 * i - 1) - q.val = i by omega,
                  Nat.mod_eq_of_lt (by omega)]
          rw [h2]; omega
      · -- 2*i ≤ d < 3*i - 1, so d' = (p - q) mod (3i - 1) ∈ [1, i - 1]: let r = (p + i) % (3i - 1)
        let d' := (p.val + (3 * i - 1) - q.val) % (3 * i - 1)
        have hd'_sum : d + d' = 3 * i - 1 := by
          have hp := p.isLt; have hq := q.isLt
          by_cases hle : p.val ≤ q.val
          · have hd_e : d = q.val - p.val := by
              have : q.val + (3 * i - 1) - p.val = (q.val - p.val) + (3 * i - 1) := by omega
              dsimp only [d]; rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have hd'_e : d' = p.val + (3 * i - 1) - q.val := Nat.mod_eq_of_lt (by omega)
            omega
          · have hd_e : d = q.val + (3 * i - 1) - p.val := Nat.mod_eq_of_lt (by omega)
            have hd'_e : d' = p.val - q.val := by
              have : p.val + (3 * i - 1) - q.val = (p.val - q.val) + (3 * i - 1) := by omega
              dsimp only [d']; rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
        let rv := (p.val + i) % (3 * i - 1)
        have hrv_lt : rv < 3 * i - 1 := Nat.mod_lt _ hm_pos
        have hrv_ne : rv ≠ 2 * i - 1 := by
          intro hrv; dsimp only [rv] at hrv
          have hp := p.isLt; have hq := q.isLt
          have hpeq : p.val = i - 1 := by
            by_cases hp2 : p.val + i < 3 * i - 1
            · rw [Nat.mod_eq_of_lt hp2] at hrv; omega
            · have : p.val + i = (p.val + i - (3 * i - 1)) + (3 * i - 1) := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hrv; omega
          have hqlt : q.val < i := by
            by_cases hle : q.val ≤ p.val
            · omega
            · have : p.val + (3 * i - 1) - q.val < 3 * i - 1 := by omega
              have hd'_e : d' = p.val + (3 * i - 1) - q.val := Nat.mod_eq_of_lt this
              omega
          exact hR ⟨by omega, hqlt⟩
        refine ⟨Sum.inl ⟨rv, hrv_lt⟩, fun _ => hrv_ne, ?_, ?_⟩
        · dsimp only
          have h1 : (rv + (3 * i - 1) - p.val) % (3 * i - 1) = i := by
            have hp := p.isLt
            by_cases hpi : p.val + i < 3 * i - 1
            · have hrv_e : rv = p.val + i := Nat.mod_eq_of_lt hpi
              rw [hrv_e, show p.val + i + (3 * i - 1) - p.val = i + (3 * i - 1) by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            · have hrv_e : rv = p.val + i - (3 * i - 1) := by
                have : p.val + i = (p.val + i - (3 * i - 1)) + (3 * i - 1) := by omega
                dsimp only [rv]; rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
              rw [hrv_e, show p.val + i - (3 * i - 1) + (3 * i - 1) - p.val = i by omega,
                  Nat.mod_eq_of_lt (by omega)]
          rw [h1]; omega
        · dsimp only
          have h2 : (rv + (3 * i - 1) - q.val) % (3 * i - 1) = d' + i := by
            have hp := p.isLt; have hq := q.isLt
            have hmod : (rv + (3 * i - 1) - q.val) % (3 * i - 1) =
                ((p.val + (3 * i - 1) - q.val) + i) % (3 * i - 1) := by
              by_cases hpi : p.val + i < 3 * i - 1
              · have hrv_e : rv = p.val + i := Nat.mod_eq_of_lt hpi
                rw [hrv_e]; congr 1; omega
              · have hrv_e : rv = p.val + i - (3 * i - 1) := by
                  have : p.val + i = (p.val + i - (3 * i - 1)) + (3 * i - 1) := by omega
                  dsimp only [rv]; rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
                rw [hrv_e]
                have heq : p.val + (3 * i - 1) - q.val + i =
                    (p.val + i - (3 * i - 1) + (3 * i - 1) - q.val) + (3 * i - 1) := by omega
                rw [heq, Nat.add_mod_right]
            rw [hmod, Nat.add_mod, show (p.val + (3 * i - 1) - q.val) % (3 * i - 1) = d' from rfl,
                Nat.mod_eq_of_lt (by omega : i < 3 * i - 1), Nat.mod_eq_of_lt (by omega)]
          rw [h2]; omega
    | inr t =>
      by_cases hp1 : p.val < i
      · fin_cases t
        · exact absurd (Or.inl ⟨Or.inl rfl, hp1⟩) hnadj
        · exact ⟨Sum.inr 0, by simp, Or.inl ⟨Or.inl rfl, hp1⟩, Or.inl (by decide)⟩
        · exact ⟨Sum.inr 3, by simp, Or.inl ⟨Or.inr rfl, hp1⟩, Or.inl (by decide)⟩
        · exact absurd (Or.inl ⟨Or.inr rfl, hp1⟩) hnadj
        · exact ⟨Sum.inr 3, by simp, Or.inl ⟨Or.inr rfl, hp1⟩, Or.inl (by decide)⟩
        · exact ⟨Sum.inr 0, by simp, Or.inl ⟨Or.inl rfl, hp1⟩, Or.inl (by decide)⟩
        · exact ⟨Sum.inr 0, by simp, Or.inl ⟨Or.inl rfl, hp1⟩, Or.inr (Or.inl (by decide))⟩
        · exact ⟨Sum.inr 3, by simp, Or.inl ⟨Or.inr rfl, hp1⟩, Or.inr (Or.inr (Or.inr (Or.inl (by decide))))⟩
      · by_cases hp2 : p.val < 2 * i
        · fin_cases t
          · exact ⟨Sum.inr 1, by simp, Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩), Or.inl (by decide)⟩
          · exact absurd (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩)) hnadj
          · exact ⟨Sum.inr 1, by simp, Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩), Or.inl (by decide)⟩
          · exact ⟨Sum.inr 4, by simp, Or.inr (Or.inl ⟨Or.inl rfl, by omega, hp2⟩), Or.inl (by decide)⟩
          · exact absurd (Or.inr (Or.inl ⟨Or.inl rfl, by omega, hp2⟩)) hnadj
          · exact ⟨Sum.inr 4, by simp, Or.inr (Or.inl ⟨Or.inl rfl, by omega, hp2⟩), Or.inl (by decide)⟩
          · exact ⟨Sum.inr 4, by simp, Or.inr (Or.inl ⟨Or.inl rfl, by omega, hp2⟩), Or.inr (Or.inl (by decide))⟩
          · exact ⟨Sum.inr 1, by simp, Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩), Or.inr (Or.inr (Or.inr (Or.inl (by decide))))⟩
        · fin_cases t
          · exact ⟨Sum.inr 5, by simp, Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩), Or.inl (by decide)⟩
          · exact ⟨Sum.inr 2, by simp, Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩), Or.inl (by decide)⟩
          · exact absurd (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)) hnadj
          · exact ⟨Sum.inr 2, by simp, Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩), Or.inl (by decide)⟩
          · exact ⟨Sum.inr 5, by simp, Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩), Or.inl (by decide)⟩
          · exact absurd (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)) hnadj
          · exact ⟨Sum.inr 2, by simp, Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩), Or.inr (Or.inl (by decide))⟩
          · exact ⟨Sum.inr 5, by simp, Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩), Or.inr (Or.inr (Or.inr (Or.inl (by decide))))⟩
  | inr t =>
    cases b with
    | inl p =>
      by_cases hp1 : p.val < i
      · fin_cases t
        · exact absurd (Or.inl ⟨Or.inl rfl, hp1⟩) hnadj
        · exact ⟨Sum.inr 0, by simp, Or.inl (by decide), Or.inl ⟨Or.inl rfl, hp1⟩⟩
        · exact ⟨Sum.inr 3, by simp, Or.inl (by decide), Or.inl ⟨Or.inr rfl, hp1⟩⟩
        · exact absurd (Or.inl ⟨Or.inr rfl, hp1⟩) hnadj
        · exact ⟨Sum.inr 3, by simp, Or.inl (by decide), Or.inl ⟨Or.inr rfl, hp1⟩⟩
        · exact ⟨Sum.inr 0, by simp, Or.inl (by decide), Or.inl ⟨Or.inl rfl, hp1⟩⟩
        · exact ⟨Sum.inr 0, by simp, Or.inr (Or.inl (by decide)), Or.inl ⟨Or.inl rfl, hp1⟩⟩
        · exact ⟨Sum.inr 3, by simp, Or.inr (Or.inr (Or.inr (Or.inl (by decide)))), Or.inl ⟨Or.inr rfl, hp1⟩⟩
      · by_cases hp2 : p.val < 2 * i
        · fin_cases t
          · exact ⟨Sum.inr 1, by simp, Or.inl (by decide), Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩)⟩
          · exact absurd (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩)) hnadj
          · exact ⟨Sum.inr 1, by simp, Or.inl (by decide), Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩)⟩
          · exact ⟨Sum.inr 4, by simp, Or.inl (by decide), Or.inr (Or.inl ⟨Or.inl rfl, by omega, hp2⟩)⟩
          · exact absurd (Or.inr (Or.inl ⟨Or.inl rfl, by omega, hp2⟩)) hnadj
          · exact ⟨Sum.inr 4, by simp, Or.inl (by decide), Or.inr (Or.inl ⟨Or.inl rfl, by omega, hp2⟩)⟩
          · exact ⟨Sum.inr 4, by simp, Or.inr (Or.inl (by decide)), Or.inr (Or.inl ⟨Or.inl rfl, by omega, hp2⟩)⟩
          · exact ⟨Sum.inr 1, by simp, Or.inr (Or.inr (Or.inr (Or.inl (by decide)))), Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩)⟩
        · fin_cases t
          · exact ⟨Sum.inr 5, by simp, Or.inl (by decide), Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)⟩
          · exact ⟨Sum.inr 2, by simp, Or.inl (by decide), Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)⟩
          · exact absurd (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)) hnadj
          · exact ⟨Sum.inr 2, by simp, Or.inl (by decide), Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)⟩
          · exact ⟨Sum.inr 5, by simp, Or.inl (by decide), Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)⟩
          · exact absurd (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)) hnadj
          · exact ⟨Sum.inr 2, by simp, Or.inr (Or.inl (by decide)), Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)⟩
          · exact ⟨Sum.inr 5, by simp, Or.inr (Or.inr (Or.inr (Or.inl (by decide)))), Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)⟩
    | inr t₂ =>
      have htne : t ≠ t₂ := fun h => hne (congrArg Sum.inr h)
      rcases ext_common_nbr t t₂ htne hnadj with ⟨r, hr7, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨Sum.inr r, fun _ => hr7, h1, h2⟩
      · exact ⟨Sum.inl ⟨0, by omega⟩, fun _ => by dsimp; omega, Or.inl ⟨h1, by dsimp; omega⟩, Or.inl ⟨h2, by dsimp; omega⟩⟩
      · exact ⟨Sum.inl ⟨i, by omega⟩, fun _ => by dsimp; omega,
          Or.inr (Or.inl ⟨h1, le_refl i, by dsimp; omega⟩), Or.inr (Or.inl ⟨h2, le_refl i, by dsimp; omega⟩)⟩
      · exact ⟨Sum.inl ⟨2 * i, by omega⟩, fun _ => by dsimp; omega,
          Or.inr (Or.inr ⟨h1, le_refl _⟩), Or.inr (Or.inr ⟨h2, le_refl _⟩)⟩

-- Separating witness between external t₁ ≠ t₂ (when not directly adjacent)
lemma ext_sep_cases (t₁ t₂ : Fin 8) (hne : t₁ ≠ t₂)
    (hnadj : ¬ ((t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
      (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
      (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
      (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
      (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)))) :
    (∃ r s : Fin 8, r.val < 6 ∧ s.val < 6 ∧
      ((t₁.val < 6 ∧ ((t₁.val + 1) % 6 = r.val ∨ (r.val + 1) % 6 = t₁.val)) ∨
       (t₁.val = 6 ∧ (r.val = 0 ∨ r.val = 4 ∨ r.val = 2)) ∨
       (t₁.val = 7 ∧ (r.val = 3 ∨ r.val = 1 ∨ r.val = 5))) ∧
      ((t₂.val < 6 ∧ ((t₂.val + 1) % 6 = s.val ∨ (s.val + 1) % 6 = t₂.val)) ∨
       (t₂.val = 6 ∧ (s.val = 0 ∨ s.val = 4 ∨ s.val = 2)) ∨
       (t₂.val = 7 ∧ (s.val = 3 ∨ s.val = 1 ∨ s.val = 5))) ∧
      ((r.val + 1) % 6 = s.val ∨ (s.val + 1) % 6 = r.val)) ∨
    (∃ (r : Fin 8) (c : Fin 3), r.val < 6 ∧
      ((t₁.val < 6 ∧ ((t₁.val + 1) % 6 = r.val ∨ (r.val + 1) % 6 = t₁.val)) ∨
       (t₁.val = 6 ∧ (r.val = 0 ∨ r.val = 4 ∨ r.val = 2)) ∨
       (t₁.val = 7 ∧ (r.val = 3 ∨ r.val = 1 ∨ r.val = 5))) ∧
      ((c.val = 0 ∧ (t₂.val = 0 ∨ t₂.val = 3) ∧ (r.val = 0 ∨ r.val = 3)) ∨
       (c.val = 1 ∧ (t₂.val = 4 ∨ t₂.val = 1) ∧ (r.val = 4 ∨ r.val = 1)) ∨
       (c.val = 2 ∧ (t₂.val = 2 ∨ t₂.val = 5) ∧ (r.val = 2 ∨ r.val = 5)))) ∨
    (∃ (s : Fin 8) (c : Fin 3), s.val < 6 ∧
      ((t₂.val < 6 ∧ ((t₂.val + 1) % 6 = s.val ∨ (s.val + 1) % 6 = t₂.val)) ∨
       (t₂.val = 6 ∧ (s.val = 0 ∨ s.val = 4 ∨ s.val = 2)) ∨
       (t₂.val = 7 ∧ (s.val = 3 ∨ s.val = 1 ∨ s.val = 5))) ∧
      ((c.val = 0 ∧ (t₁.val = 0 ∨ t₁.val = 3) ∧ (s.val = 0 ∨ s.val = 3)) ∨
       (c.val = 1 ∧ (t₁.val = 4 ∨ t₁.val = 1) ∧ (s.val = 4 ∨ s.val = 1)) ∨
       (c.val = 2 ∧ (t₁.val = 2 ∨ t₁.val = 5) ∧ (s.val = 2 ∨ s.val = 5)))) := by
  let eadj : Fin 8 → Fin 8 → Bool := fun a b =>
    (decide (a.val < 6) && decide (b.val < 6) && ((a.val + 1) % 6 == b.val || (b.val + 1) % 6 == a.val)) ||
    (a.val == 6 && (b.val == 0 || b.val == 4 || b.val == 2 || b.val == 7)) ||
    (b.val == 6 && (a.val == 0 || a.val == 4 || a.val == 2 || a.val == 7)) ||
    (a.val == 7 && (b.val == 3 || b.val == 1 || b.val == 5 || b.val == 6)) ||
    (b.val == 7 && (a.val == 3 || a.val == 1 || a.val == 5 || a.val == 6))
  let adj6 : Fin 8 → Fin 8 → Bool := fun a r =>
    (decide (a.val < 6) && ((a.val + 1) % 6 == r.val || (r.val + 1) % 6 == a.val)) ||
    (a.val == 6 && (r.val == 0 || r.val == 4 || r.val == 2)) ||
    (a.val == 7 && (r.val == 3 || r.val == 1 || r.val == 5))
  let colm : Fin 3 → Fin 8 → Fin 8 → Bool := fun c x y =>
    (c.val == 0 && (x.val == 0 || x.val == 3) && (y.val == 0 || y.val == 3)) ||
    (c.val == 1 && (x.val == 4 || x.val == 1) && (y.val == 4 || y.val == 1)) ||
    (c.val == 2 && (x.val == 2 || x.val == 5) && (y.val == 2 || y.val == 5))
  let w : Fin 8 → Fin 8 → Fin 8 × Fin 8 × Fin 3 := fun a b => match a.val, b.val with
    | 0, 3 => (1, 2, 0) | 3, 0 => (2, 1, 0) | 1, 4 => (0, 5, 0) | 4, 1 => (3, 2, 0)
    | 2, 5 => (1, 0, 0) | 5, 2 => (0, 1, 0)
    | 0, 2 => (5, 0, 2) | 0, 4 => (1, 0, 1) | 1, 3 => (0, 0, 0) | 1, 5 => (2, 0, 2)
    | 2, 0 => (3, 0, 0) | 2, 4 => (1, 0, 1) | 3, 1 => (4, 0, 1) | 3, 5 => (2, 0, 2)
    | 4, 0 => (3, 0, 0) | 4, 2 => (5, 0, 2) | 5, 1 => (4, 0, 1) | 5, 3 => (0, 0, 0)
    | 6, 1 => (4, 0, 1) | 6, 3 => (0, 0, 0) | 6, 5 => (2, 0, 2)
    | 7, 0 => (3, 0, 0) | 7, 2 => (5, 0, 2) | 7, 4 => (1, 0, 1)
    | 0, 7 => (0, 3, 0) | 1, 6 => (0, 4, 1) | 2, 7 => (0, 5, 2)
    | 3, 6 => (0, 0, 0) | 4, 7 => (0, 1, 1) | 5, 6 => (0, 2, 2)
    | _, _ => (0, 0, 0)
  have he : ∀ a b : Fin 8, eadj a b = true ↔
      ((a.val < 6 ∧ b.val < 6 ∧ ((a.val + 1) % 6 = b.val ∨ (b.val + 1) % 6 = a.val)) ∨
       (a.val = 6 ∧ (b.val = 0 ∨ b.val = 4 ∨ b.val = 2 ∨ b.val = 7)) ∨
       (b.val = 6 ∧ (a.val = 0 ∨ a.val = 4 ∨ a.val = 2 ∨ a.val = 7)) ∨
       (a.val = 7 ∧ (b.val = 3 ∨ b.val = 1 ∨ b.val = 5 ∨ b.val = 6)) ∨
       (b.val = 7 ∧ (a.val = 3 ∨ a.val = 1 ∨ a.val = 5 ∨ a.val = 6))) := by
    intro a b; simp only [eadj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, or_assoc, and_assoc]
  have ha6 : ∀ a r : Fin 8, adj6 a r = true ↔
      ((a.val < 6 ∧ ((a.val + 1) % 6 = r.val ∨ (r.val + 1) % 6 = a.val)) ∨
       (a.val = 6 ∧ (r.val = 0 ∨ r.val = 4 ∨ r.val = 2)) ∨
       (a.val = 7 ∧ (r.val = 3 ∨ r.val = 1 ∨ r.val = 5))) := by
    intro a r; simp only [adj6, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, or_assoc]
  have hcm : ∀ c x y, colm c x y = true ↔
      ((c.val = 0 ∧ (x.val = 0 ∨ x.val = 3) ∧ (y.val = 0 ∨ y.val = 3)) ∨
       (c.val = 1 ∧ (x.val = 4 ∨ x.val = 1) ∧ (y.val = 4 ∨ y.val = 1)) ∨
       (c.val = 2 ∧ (x.val = 2 ∨ x.val = 5) ∧ (y.val = 2 ∨ y.val = 5))) := by
    intro c x y; simp only [colm, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc, and_assoc]
  have hok : ∀ a b : Fin 8,
      let r := (w a b).1; let s := (w a b).2.1; let c := (w a b).2.2
      (a == b || eadj a b ||
        (decide (r.val < 6) && decide (s.val < 6) && adj6 a r && adj6 b s &&
          ((r.val + 1) % 6 == s.val || (s.val + 1) % 6 == r.val)) ||
        (decide (r.val < 6) && adj6 a r && colm c b r) ||
        (decide (s.val < 6) && adj6 b s && colm c a s)) = true := by decide
  have h := hok t₁ t₂
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ((((h | h) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩)
  · exact absurd h hne
  · exact absurd ((he t₁ t₂).mp h) hnadj
  · exact Or.inl ⟨(w t₁ t₂).1, (w t₁ t₂).2.1, h1, h2, (ha6 _ _).mp h3, (ha6 _ _).mp h4, h5⟩
  · exact Or.inr (Or.inl ⟨(w t₁ t₂).1, (w t₁ t₂).2.2, h1, (ha6 _ _).mp h2, (hcm _ _ _).mp h3⟩)
  · exact Or.inr (Or.inr ⟨(w t₁ t₂).2.1, (w t₁ t₂).2.2, h1, (ha6 _ _).mp h2, (hcm _ _ _).mp h3⟩)

-- Explicit separating edge in Fin 6 between color c ∈ {0(R), 1(G), 2(B)} and non-adjacent external t : Fin 8
lemma and_ext_sep (c : Fin 3) (t : Fin 8)
    (hnadj : ¬ ((c.val = 0 ∧ (t.val = 0 ∨ t.val = 3)) ∨
      (c.val = 1 ∧ (t.val = 4 ∨ t.val = 1)) ∨ (c.val = 2 ∧ (t.val = 2 ∨ t.val = 5)))) :
    ∃ r s : Fin 8, r.val < 6 ∧ s.val < 6 ∧
      ((c.val = 0 ∧ (r.val = 0 ∨ r.val = 3)) ∨
       (c.val = 1 ∧ (r.val = 4 ∨ r.val = 1)) ∨
       (c.val = 2 ∧ (r.val = 2 ∨ r.val = 5))) ∧
      ((t.val < 6 ∧ ((t.val + 1) % 6 = s.val ∨ (s.val + 1) % 6 = t.val)) ∨
       (t.val = 6 ∧ (s.val = 0 ∨ s.val = 4 ∨ s.val = 2)) ∨
       (t.val = 7 ∧ (s.val = 3 ∨ s.val = 1 ∨ s.val = 5))) ∧
      ((r.val + 1) % 6 = s.val ∨ (s.val + 1) % 6 = r.val) := by
  let w : Fin 3 → Fin 8 → Fin 8 × Fin 8 := fun c t => match c.val, t.val with
    | 0, 1 => (3, 2) | 0, 2 => (0, 1) | 0, 4 => (0, 5) | 0, 5 => (3, 4) | 0, 6 => (3, 2) | 0, 7 => (0, 1)
    | 1, 0 => (4, 5) | 1, 2 => (4, 3) | 1, 3 => (1, 2) | 1, 5 => (1, 0) | 1, 6 => (1, 0) | 1, 7 => (4, 3)
    | 2, 0 => (2, 1) | 2, 1 => (5, 0) | 2, 3 => (5, 4) | 2, 4 => (2, 3) | 2, 6 => (5, 0) | 2, 7 => (2, 1)
    | _, _ => (0, 0)
  have hcheck : ∀ c : Fin 3, ∀ t : Fin 8,
      ¬ ((c.val = 0 ∧ (t.val = 0 ∨ t.val = 3)) ∨
        (c.val = 1 ∧ (t.val = 4 ∨ t.val = 1)) ∨ (c.val = 2 ∧ (t.val = 2 ∨ t.val = 5))) →
      let r := (w c t).1; let s := (w c t).2
      r.val < 6 ∧ s.val < 6 ∧
      ((c.val = 0 ∧ (r.val = 0 ∨ r.val = 3)) ∨
       (c.val = 1 ∧ (r.val = 4 ∨ r.val = 1)) ∨
       (c.val = 2 ∧ (r.val = 2 ∨ r.val = 5))) ∧
      ((t.val < 6 ∧ ((t.val + 1) % 6 = s.val ∨ (s.val + 1) % 6 = t.val)) ∨
       (t.val = 6 ∧ (s.val = 0 ∨ s.val = 4 ∨ s.val = 2)) ∨
       (t.val = 7 ∧ (s.val = 3 ∨ s.val = 1 ∨ s.val = 5))) ∧
      ((r.val + 1) % 6 = s.val ∨ (s.val + 1) % 6 = r.val) := by decide
  exact ⟨(w c t).1, (w c t).2, hcheck c t hnadj⟩

-- Every homomorphism from Υ_i^{μν} to a triangle-free graph G is automatically induced.
lemma vega_hom_induced {V : Type} {G : SimpleGraph V} (hcf : G.CliqueFree 3)
    {i : ℕ} (hi : 2 ≤ i) {μ ν : Bool} {f : Fin (3 * i - 1) ⊕ Fin 8 → V}
    (hf : ∀ a b,
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) a) →
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) b) →
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q =>
            i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
            (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ =>
            (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
            (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
            (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
            (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
            (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b) →
      G.Adj (f a) (f b))
    {a b : Fin (3 * i - 1) ⊕ Fin 8}
    (ha : (fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) a)
    (hb : (fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) b)
    (hadj : G.Adj (f a) (f b)) :
    (fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b := by
  by_contra hnadj
  have hne : a ≠ b := fun h => by subst h; exact G.loopless.irrefl _ hadj
  obtain ⟨r, hr, har, hbr⟩ := vega_maximal_tf hi μ ν a b ha hb hne hnadj
  exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf
    (hf a r ha hr har).symm (hf b r hb hr hbr).symm hadj

-- Every homomorphism from Υ_i^{μν} to a triangle-free graph G is automatically injective on active vertices.
lemma vega_hom_injective {V : Type} {G : SimpleGraph V} (hcf : G.CliqueFree 3)
    {i : ℕ} (hi : 2 ≤ i) {μ ν : Bool} {f : Fin (3 * i - 1) ⊕ Fin 8 → V}
    (hf : ∀ a b,
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) a) →
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) b) →
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q =>
            i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
            (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ =>
            (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
            (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
            (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
            (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
            (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b) →
      G.Adj (f a) (f b))
    {a b : Fin (3 * i - 1) ⊕ Fin 8}
    (ha : (fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) a)
    (hb : (fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) b)
    (hfeq : f a = f b) : a = b := by
  by_contra hne
  have sep : ∀ r s : Fin (3 * i - 1) ⊕ Fin 8,
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) r) →
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) s) →
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q => i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t => ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨ ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨ ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p => ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨ ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨ ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ => (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨ (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨ (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨ (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨ (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a r) →
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q => i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t => ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨ ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨ ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p => ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨ ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨ ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ => (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨ (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨ (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨ (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨ (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) b s) →
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q => i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t => ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨ ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨ ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p => ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨ ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨ ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ => (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨ (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨ (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨ (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨ (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) r s) →
      False := by
    intro r s hr hs har hbs hrs
    have h1 := hf a r ha hr har
    have h2 := hf b s hb hs hbs
    rw [← hfeq] at h2
    exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf h1 h2 (hf r s hr hs hrs)
  have ext_lift : ∀ t r : Fin 8, r.val < 6 →
      ((t.val < 6 ∧ ((t.val + 1) % 6 = r.val ∨ (r.val + 1) % 6 = t.val)) ∨
       (t.val = 6 ∧ (r.val = 0 ∨ r.val = 4 ∨ r.val = 2)) ∨
       (t.val = 7 ∧ (r.val = 3 ∨ r.val = 1 ∨ r.val = 5))) →
      (t.val < 6 ∧ r.val < 6 ∧ ((t.val + 1) % 6 = r.val ∨ (r.val + 1) % 6 = t.val)) ∨
      (t.val = 6 ∧ (r.val = 0 ∨ r.val = 4 ∨ r.val = 2 ∨ r.val = 7)) ∨
      (r.val = 6 ∧ (t.val = 0 ∨ t.val = 4 ∨ t.val = 2 ∨ t.val = 7)) ∨
      (t.val = 7 ∧ (r.val = 3 ∨ r.val = 1 ∨ r.val = 5 ∨ r.val = 6)) ∨
      (r.val = 7 ∧ (t.val = 3 ∨ t.val = 1 ∨ t.val = 5 ∨ t.val = 6)) := by
    intro t r hr h
    rcases h with ⟨ht, h1⟩ | ⟨ht, h1 | h1 | h1⟩ | ⟨ht, h1 | h1 | h1⟩
    · exact Or.inl ⟨ht, hr, h1⟩
    · exact Or.inr (Or.inl ⟨ht, Or.inl h1⟩)
    · exact Or.inr (Or.inl ⟨ht, Or.inr (Or.inl h1)⟩)
    · exact Or.inr (Or.inl ⟨ht, Or.inr (Or.inr (Or.inl h1))⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, Or.inl h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, Or.inr (Or.inl h1)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, Or.inr (Or.inr (Or.inl h1))⟩)))
  have hnot_adj : ¬ (match a, b with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) := fun hadj => by
    have := hf a b ha hb hadj
    rw [hfeq] at this
    exact G.loopless.irrefl _ this
  cases a with
  | inl p =>
    cases b with
    | inl q =>
      have hpq : p.val ≠ q.val := fun h => hne (congrArg Sum.inl (Fin.ext h))
      -- Helper for ordered pair p < q in the same color
      have same_col : ∀ (x y : Fin (3 * i - 1)), x.val < y.val →
          (f (Sum.inl x) = f (Sum.inl y)) →
          (ν = true → x.val ≠ 2 * i - 1) → (ν = true → y.val ≠ 2 * i - 1) →
          (x.val < i ∧ y.val < i) ∨ ((i ≤ x.val ∧ x.val < 2 * i) ∧ (i ≤ y.val ∧ y.val < 2 * i)) ∨
          (2 * i ≤ x.val ∧ 2 * i ≤ y.val) → False := by
        intro x y hxy hxyeq hx hy hcol
        have hlt_x := x.isLt; have hlt_y := y.isLt
        rcases hcol with ⟨hx1, hy1⟩ | ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ | ⟨hx1, hy1⟩
        · let r : Fin (3 * i - 1) := ⟨x.val + i, by omega⟩
          let s : Fin (3 * i - 1) := ⟨y.val + 2 * i - 1, by omega⟩
          have hr_act : ν = true → r.val ≠ 2 * i - 1 := fun _ => by simp [r]; omega
          have hs_act : ν = true → s.val ≠ 2 * i - 1 := fun _ => by simp [s]; omega
          have hxr : G.Adj (f (Sum.inl x)) (f (Sum.inl r)) := hf _ _ hx hr_act (by
            dsimp only
            have : r.val + (3 * i - 1) - x.val = i + (3 * i - 1) := by simp [r]; omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
          have hys : G.Adj (f (Sum.inl y)) (f (Sum.inl s)) := hf _ _ hy hs_act (by
            dsimp only
            have : s.val + (3 * i - 1) - y.val = (2 * i - 1) + (3 * i - 1) := by simp [s]; omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
          have hrs : G.Adj (f (Sum.inl r)) (f (Sum.inl s)) := hf _ _ hr_act hs_act (by
            dsimp only
            have : s.val + (3 * i - 1) - r.val = (y.val - x.val + i - 1) + (3 * i - 1) := by simp [r, s]; omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
          rw [← hxyeq] at hys
          exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf hxr hys hrs
        · let r : Fin (3 * i - 1) := ⟨x.val + i, by omega⟩
          let s : Fin (3 * i - 1) := ⟨y.val - i, by omega⟩
          have hr_act : ν = true → r.val ≠ 2 * i - 1 := fun _ => by simp [r]; omega
          have hs_act : ν = true → s.val ≠ 2 * i - 1 := fun _ => by simp [s]; omega
          have hxr : G.Adj (f (Sum.inl x)) (f (Sum.inl r)) := hf _ _ hx hr_act (by
            dsimp only
            have : r.val + (3 * i - 1) - x.val = i + (3 * i - 1) := by simp [r]; omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
          have hys : G.Adj (f (Sum.inl y)) (f (Sum.inl s)) := hf _ _ hy hs_act (by
            dsimp only
            have : s.val + (3 * i - 1) - y.val = 2 * i - 1 := by simp [s]; omega
            rw [this, Nat.mod_eq_of_lt (by omega)]; omega)
          have hsr : G.Adj (f (Sum.inl s)) (f (Sum.inl r)) := hf _ _ hs_act hr_act (by
            dsimp only
            have : r.val + (3 * i - 1) - s.val = (2 * i - (y.val - x.val)) + (3 * i - 1) := by simp [r, s]; omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
          rw [← hxyeq] at hys
          exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf hxr hys hsr.symm
        · let r : Fin (3 * i - 1) := ⟨x.val - 2 * i + 1, by omega⟩
          let s : Fin (3 * i - 1) := ⟨y.val - i, by omega⟩
          have hr_act : ν = true → r.val ≠ 2 * i - 1 := fun _ => by simp [r]; omega
          have hs_act : ν = true → s.val ≠ 2 * i - 1 := fun _ => by simp [s]; omega
          have hxr : G.Adj (f (Sum.inl x)) (f (Sum.inl r)) := hf _ _ hx hr_act (by
            dsimp only
            have : r.val + (3 * i - 1) - x.val = i := by simp [r]; omega
            rw [this, Nat.mod_eq_of_lt (by omega)]; omega)
          have hys : G.Adj (f (Sum.inl y)) (f (Sum.inl s)) := hf _ _ hy hs_act (by
            dsimp only
            have : s.val + (3 * i - 1) - y.val = 2 * i - 1 := by simp [s]; omega
            rw [this, Nat.mod_eq_of_lt (by omega)]; omega)
          have hrs : G.Adj (f (Sum.inl r)) (f (Sum.inl s)) := hf _ _ hr_act hs_act (by
            dsimp only
            have : s.val + (3 * i - 1) - r.val = (y.val - x.val + i - 1) + (3 * i - 1) := by simp [r, s]; omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
          rw [← hxyeq] at hys
          exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf hxr hys hrs
      by_cases hR : p.val < i ∧ q.val < i
      · rcases lt_or_gt_of_ne hpq with hlt | hgt
        · exact same_col p q hlt hfeq ha hb (Or.inl hR)
        · exact same_col q p hgt hfeq.symm hb ha (Or.inl ⟨hR.2, hR.1⟩)
      by_cases hG : (i ≤ p.val ∧ p.val < 2 * i) ∧ (i ≤ q.val ∧ q.val < 2 * i)
      · rcases lt_or_gt_of_ne hpq with hlt | hgt
        · exact same_col p q hlt hfeq ha hb (Or.inr (Or.inl hG))
        · exact same_col q p hgt hfeq.symm hb ha (Or.inr (Or.inl ⟨hG.2, hG.1⟩))
      by_cases hB : 2 * i ≤ p.val ∧ 2 * i ≤ q.val
      · rcases lt_or_gt_of_ne hpq with hlt | hgt
        · exact same_col p q hlt hfeq ha hb (Or.inr (Or.inr hB))
        · exact same_col q p hgt hfeq.symm hb ha (Or.inr (Or.inr ⟨hB.2, hB.1⟩))
      -- Different colors -> adjacent hexagon vertices
      by_cases hp1 : p.val < i
      · by_cases hq2 : q.val < 2 * i
        · exact sep (Sum.inr 0) (Sum.inr 1) (by simp) (by simp)
            (Or.inl ⟨Or.inl rfl, hp1⟩) (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hq2⟩)) (Or.inl (by decide))
        · exact sep (Sum.inr 0) (Sum.inr 5) (by simp) (by simp)
            (Or.inl ⟨Or.inl rfl, hp1⟩) (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)) (Or.inl (by decide))
      · by_cases hp2 : p.val < 2 * i
        · by_cases hq1 : q.val < i
          · exact sep (Sum.inr 1) (Sum.inr 0) (by simp) (by simp)
              (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩)) (Or.inl ⟨Or.inl rfl, hq1⟩) (Or.inl (by decide))
          · exact sep (Sum.inr 1) (Sum.inr 2) (by simp) (by simp)
              (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hp2⟩)) (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)) (Or.inl (by decide))
        · by_cases hq1 : q.val < i
          · exact sep (Sum.inr 5) (Sum.inr 0) (by simp) (by simp)
              (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)) (Or.inl ⟨Or.inl rfl, hq1⟩) (Or.inl (by decide))
          · exact sep (Sum.inr 2) (Sum.inr 1) (by simp) (by simp)
              (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)) (Or.inr (Or.inl ⟨Or.inr rfl, by omega, by omega⟩)) (Or.inl (by decide))
    | inr t =>
      by_cases hp1 : p.val < i
      · obtain ⟨r, s, hr6, hs6, hcr, hts, hrs⟩ := and_ext_sep 0 t (by
          intro h; rcases h with ⟨_, ht⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact hnot_adj (Or.inl ⟨ht, hp1⟩)
          · simp at h
          · simp at h)
        exact sep (Sum.inr r) (Sum.inr s) (fun _ => by omega) (fun _ => by omega)
          (by rcases hcr with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact Or.inl ⟨h, hp1⟩; simp at h; simp at h)
          (ext_lift t s hs6 hts) (Or.inl ⟨hr6, hs6, hrs⟩)
      · by_cases hp2 : p.val < 2 * i
        · obtain ⟨r, s, hr6, hs6, hcr, hts, hrs⟩ := and_ext_sep 1 t (by
            intro h; rcases h with ⟨h, _⟩ | ⟨_, ht⟩ | ⟨h, _⟩
            · simp at h
            · exact hnot_adj (Or.inr (Or.inl ⟨ht, by omega, hp2⟩))
            · simp at h)
          exact sep (Sum.inr r) (Sum.inr s) (fun _ => by omega) (fun _ => by omega)
            (by rcases hcr with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; simp at h; exact Or.inr (Or.inl ⟨h, by omega, hp2⟩); simp at h)
            (ext_lift t s hs6 hts) (Or.inl ⟨hr6, hs6, hrs⟩)
        · obtain ⟨r, s, hr6, hs6, hcr, hts, hrs⟩ := and_ext_sep 2 t (by
            intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, ht⟩
            · simp at h
            · simp at h
            · exact hnot_adj (Or.inr (Or.inr ⟨ht, by omega⟩)))
          exact sep (Sum.inr r) (Sum.inr s) (fun _ => by omega) (fun _ => by omega)
            (by rcases hcr with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩; simp at h; simp at h; exact Or.inr (Or.inr ⟨h, by omega⟩))
            (ext_lift t s hs6 hts) (Or.inl ⟨hr6, hs6, hrs⟩)
  | inr t =>
    cases b with
    | inl p =>
      by_cases hp1 : p.val < i
      · obtain ⟨r, s, hr6, hs6, hcr, hts, hrs⟩ := and_ext_sep 0 t (by
          intro h; rcases h with ⟨_, ht⟩ | ⟨h, _⟩ | ⟨h, _⟩
          · exact hnot_adj (Or.inl ⟨ht, hp1⟩)
          · simp at h
          · simp at h)
        exact sep (Sum.inr s) (Sum.inr r) (fun _ => by omega) (fun _ => by omega)
          (ext_lift t s hs6 hts)
          (by rcases hcr with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact Or.inl ⟨h, hp1⟩; simp at h; simp at h)
          (Or.inl ⟨hs6, hr6, hrs.symm⟩)
      · by_cases hp2 : p.val < 2 * i
        · obtain ⟨r, s, hr6, hs6, hcr, hts, hrs⟩ := and_ext_sep 1 t (by
            intro h; rcases h with ⟨h, _⟩ | ⟨_, ht⟩ | ⟨h, _⟩
            · simp at h
            · exact hnot_adj (Or.inr (Or.inl ⟨ht, by omega, hp2⟩))
            · simp at h)
          exact sep (Sum.inr s) (Sum.inr r) (fun _ => by omega) (fun _ => by omega)
            (ext_lift t s hs6 hts)
            (by rcases hcr with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; simp at h; exact Or.inr (Or.inl ⟨h, by omega, hp2⟩); simp at h)
            (Or.inl ⟨hs6, hr6, hrs.symm⟩)
        · obtain ⟨r, s, hr6, hs6, hcr, hts, hrs⟩ := and_ext_sep 2 t (by
            intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, ht⟩
            · simp at h
            · simp at h
            · exact hnot_adj (Or.inr (Or.inr ⟨ht, by omega⟩)))
          exact sep (Sum.inr s) (Sum.inr r) (fun _ => by omega) (fun _ => by omega)
            (ext_lift t s hs6 hts)
            (by rcases hcr with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩; simp at h; simp at h; exact Or.inr (Or.inr ⟨h, by omega⟩))
            (Or.inl ⟨hs6, hr6, hrs.symm⟩)
    | inr t₂ =>
      have htne : t ≠ t₂ := fun h => hne (congrArg Sum.inr h)
      rcases ext_sep_cases t t₂ htne hnot_adj with
        ⟨r, s, hr6, hs6, h1, h2, h3⟩ | ⟨r, c, hr6, h1, hc⟩ | ⟨s, c, hs6, h2, hc⟩
      · exact sep (Sum.inr r) (Sum.inr s) (fun _ => by omega) (fun _ => by omega)
          (ext_lift t r hr6 h1) (ext_lift t₂ s hs6 h2) (Or.inl ⟨hr6, hs6, h3⟩)
      · rcases hc with ⟨_, ht2, hr⟩ | ⟨_, ht2, hr⟩ | ⟨_, ht2, hr⟩
        · exact sep (Sum.inr r) (Sum.inl ⟨0, by omega⟩) (fun _ => by omega) (fun _ => by dsimp; omega)
            (ext_lift t r hr6 h1) (Or.inl ⟨ht2, by dsimp; omega⟩) (Or.inl ⟨hr, by dsimp; omega⟩)
        · exact sep (Sum.inr r) (Sum.inl ⟨i, by omega⟩) (fun _ => by omega) (fun _ => by dsimp; omega)
            (ext_lift t r hr6 h1) (Or.inr (Or.inl ⟨ht2, le_refl i, by dsimp; omega⟩))
            (Or.inr (Or.inl ⟨hr, le_refl i, by dsimp; omega⟩))
        · exact sep (Sum.inr r) (Sum.inl ⟨2 * i, by omega⟩) (fun _ => by omega) (fun _ => by dsimp; omega)
            (ext_lift t r hr6 h1) (Or.inr (Or.inr ⟨ht2, le_refl _⟩))
            (Or.inr (Or.inr ⟨hr, le_refl _⟩))
      · rcases hc with ⟨_, ht1, hs⟩ | ⟨_, ht1, hs⟩ | ⟨_, ht1, hs⟩
        · exact sep (Sum.inl ⟨0, by omega⟩) (Sum.inr s) (fun _ => by dsimp; omega) (fun _ => by omega)
            (Or.inl ⟨ht1, by dsimp; omega⟩) (ext_lift t₂ s hs6 h2) (Or.inl ⟨hs, by dsimp; omega⟩)
        · exact sep (Sum.inl ⟨i, by omega⟩) (Sum.inr s) (fun _ => by dsimp; omega) (fun _ => by omega)
            (Or.inr (Or.inl ⟨ht1, le_refl i, by dsimp; omega⟩)) (ext_lift t₂ s hs6 h2)
            (Or.inr (Or.inl ⟨hs, le_refl i, by dsimp; omega⟩))
        · exact sep (Sum.inl ⟨2 * i, by omega⟩) (Sum.inr s) (fun _ => by dsimp; omega) (fun _ => by omega)
            (Or.inr (Or.inr ⟨ht1, le_refl _⟩)) (ext_lift t₂ s hs6 h2)
            (Or.inr (Or.inr ⟨hs, le_refl _⟩))

-- Upper bound on the order of any Vega subgraph in a finite triangle-free graph.
lemma vega_card_le {V : Type} [Fintype V] {G : SimpleGraph V} (hcf : G.CliqueFree 3)
    {i : ℕ} (hi : 2 ≤ i) {μ ν : Bool} {f : Fin (3 * i - 1) ⊕ Fin 8 → V}
    (hf : ∀ a b,
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) a) →
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) b) →
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q =>
            i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
            (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ =>
            (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
            (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
            (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
            (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
            (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b) →
      G.Adj (f a) (f b)) :
    3 * i + 7 - μ.toNat - ν.toNat ≤ Fintype.card V := by
  classical
  let actS : Finset (Fin (3 * i - 1) ⊕ Fin 8) := Finset.univ.filter fun a =>
    match a with
    | Sum.inl p => ν = true → p.val ≠ 2 * i - 1
    | Sum.inr t => μ = true → t.val ≠ 7
  have hcard_le : actS.card ≤ Fintype.card V := by
    have hinj : Set.InjOn f (actS : Set (Fin (3 * i - 1) ⊕ Fin 8)) := by
      intro a ha b hb hfeq
      simp only [Finset.mem_coe, actS, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact vega_hom_injective hcf hi hf ha hb hfeq
    calc actS.card = (actS.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card V := Finset.card_univ
  have hact_card : actS.card = 3 * i + 7 - μ.toNat - ν.toNat := by
    let inlS : Finset (Fin (3 * i - 1)) :=
      Finset.univ.filter fun p => ν = true → p.val ≠ 2 * i - 1
    let inrS : Finset (Fin 8) :=
      Finset.univ.filter fun t => μ = true → t.val ≠ 7
    have hsplit : actS = inlS.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        inrS.map ⟨Sum.inr, Sum.inr_injective⟩ := by
      ext x; cases x <;> simp [actS, inlS, inrS]
    have hdisj : Disjoint (inlS.map ⟨Sum.inl, Sum.inl_injective⟩)
        (inrS.map ⟨Sum.inr, Sum.inr_injective⟩) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx1 hx2
      rcases hx1 with ⟨_, _, rfl⟩; rcases hx2 with ⟨_, _, h⟩; cases h
    rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
    have hinl : inlS.card = 3 * i - 1 - ν.toNat := by
      cases ν
      · simp [inlS]
      · have hsub : inlS = Finset.univ.erase ⟨2 * i - 1, by omega⟩ := by
          ext p; simp [inlS, Fin.ext_iff]
        rw [hsub, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        simp
    have hinr : inrS.card = 8 - μ.toNat := by
      cases μ
      · simp [inrS]
      · have hsub : inrS = Finset.univ.erase ⟨7, by omega⟩ := by
          ext t; simp [inrS, Fin.ext_iff]
        rw [hsub, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        simp
    rw [hinl, hinr]; cases μ <;> cases ν <;> simp <;> omega
  omega

/- ### Part 6: Grötzsch ≅ Υ_2^{11} Isomorphism & Existence of Maximal Vega Subgraph -/

lemma grotzsch_to_vega211 {V : Type} {G : SimpleGraph V}
    (v u : Fin 5 → V) (w : V)
    (hg : ∀ k : Fin 5,
      G.Adj (v k) (v (k + 1)) ∧ G.Adj (u k) (v (k + 1)) ∧
      G.Adj (u k) (v (k + 4)) ∧ G.Adj w (u k)) :
    ∃ f : Fin (3 * 2 - 1) ⊕ Fin 8 → V,
      ∀ a b,
        ((fun x : Fin (3 * 2 - 1) ⊕ Fin 8 => match x with | Sum.inl p => true = true → p.val ≠ 2 * 2 - 1 | Sum.inr t => true = true → t.val ≠ 7) a) →
        ((fun x : Fin (3 * 2 - 1) ⊕ Fin 8 => match x with | Sum.inl p => true = true → p.val ≠ 2 * 2 - 1 | Sum.inr t => true = true → t.val ≠ 7) b) →
        ((fun x y : Fin (3 * 2 - 1) ⊕ Fin 8 => match x, y with
          | Sum.inl p, Sum.inl q =>
              2 ≤ (q.val + (3 * 2 - 1) - p.val) % (3 * 2 - 1) ∧
              (q.val + (3 * 2 - 1) - p.val) % (3 * 2 - 1) ≤ 2 * 2 - 1
          | Sum.inl p, Sum.inr t =>
              ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
              ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 2 * 2) ∨
              ((t.val = 2 ∨ t.val = 5) ∧ 2 * 2 ≤ p.val)
          | Sum.inr t, Sum.inl p =>
              ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
              ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 2 * 2) ∨
              ((t.val = 2 ∨ t.val = 5) ∧ 2 * 2 ≤ p.val)
          | Sum.inr t₁, Sum.inr t₂ =>
              (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
              (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
              (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
              (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
              (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b) →
        G.Adj (f a) (f b) := by
  let f : Fin 5 ⊕ Fin 8 → V := fun x => match x with
    | Sum.inl p => ![u 4, u 2, v 0, w, v 1] p
    | Sum.inr t => ![w, u 1, v 2, v 3, v 4, u 0, u 3, w] t
  refine ⟨f, fun a b ha hb hadj => ?_⟩
  have hv01 := (hg 0).1; have hv12 := (hg 1).1; have hv23 := (hg 2).1
  have hv34 := (hg 3).1; have hv40 := (hg 4).1
  have hu0_1 := (hg 0).2.1; have hu0_4 := (hg 0).2.2.1; have hwu0 := (hg 0).2.2.2
  have hu1_2 := (hg 1).2.1; have hu1_0 := (hg 1).2.2.1; have hwu1 := (hg 1).2.2.2
  have hu2_3 := (hg 2).2.1; have hu2_1 := (hg 2).2.2.1; have hwu2 := (hg 2).2.2.2
  have hu3_4 := (hg 3).2.1; have hu3_2 := (hg 3).2.2.1; have hwu3 := (hg 3).2.2.2
  have hu4_0 := (hg 4).2.1; have hu4_3 := (hg 4).2.2.1; have hwu4 := (hg 4).2.2.2
  cases a with
  | inl p =>
    have hp3 : p.val ≠ 3 := ha rfl
    cases b with
    | inl q =>
      have hq3 : q.val ≠ 3 := hb rfl
      rcases p with ⟨p, hp⟩; rcases q with ⟨q, hq⟩
      dsimp only [f] at hadj ⊢
      interval_cases p <;> interval_cases q <;> first
        | exact absurd rfl hp3 | exact absurd rfl hq3
        | (exfalso; omega)
        | exact hv01 | exact hv01.symm | exact hu4_0 | exact hu4_0.symm
        | exact hu2_1 | exact hu2_1.symm
    | inr t =>
      have ht7 : t.val ≠ 7 := hb rfl
      rcases p with ⟨p, hp⟩; rcases t with ⟨t, ht⟩
      dsimp only [f] at hadj ⊢
      interval_cases p <;> interval_cases t <;> first
        | exact absurd rfl hp3 | exact absurd rfl ht7
        | (exfalso; omega)
        | exact hwu4 | exact hwu4.symm | exact hu4_3 | exact hu4_3.symm
        | exact hwu2 | exact hwu2.symm | exact hu2_3 | exact hu2_3.symm
        | exact hu1_0 | exact hu1_0.symm | exact hv40 | exact hv40.symm
        | exact hv12 | exact hv12.symm | exact hu0_1 | exact hu0_1.symm
  | inr t =>
    have ht7 : t.val ≠ 7 := ha rfl
    cases b with
    | inl p =>
      have hp3 : p.val ≠ 3 := hb rfl
      rcases t with ⟨t, ht⟩; rcases p with ⟨p, hp⟩
      dsimp only [f] at hadj ⊢
      interval_cases t <;> interval_cases p <;> first
        | exact absurd rfl hp3 | exact absurd rfl ht7
        | (exfalso; omega)
        | exact hwu4 | exact hwu4.symm | exact hu4_3 | exact hu4_3.symm
        | exact hwu2 | exact hwu2.symm | exact hu2_3 | exact hu2_3.symm
        | exact hu1_0 | exact hu1_0.symm | exact hv40 | exact hv40.symm
        | exact hv12 | exact hv12.symm | exact hu0_1
    | inr t₂ =>
      have ht27 : t₂.val ≠ 7 := hb rfl
      rcases t with ⟨t, ht⟩; rcases t₂ with ⟨t₂, ht₂⟩
      dsimp only [f] at hadj ⊢
      interval_cases t <;> interval_cases t₂ <;> first
        | exact absurd rfl ht7 | exact absurd rfl ht27
        | (exfalso; omega)
        | exact hwu1 | exact hwu1.symm | exact hwu0 | exact hwu0.symm
        | exact hwu3 | exact hwu3.symm | exact hu1_2 | exact hu1_2.symm
        | exact hv23 | exact hv23.symm | exact hu3_2 | exact hu3_2.symm
        | exact hv34 | exact hv34.symm | exact hu0_4 | exact hu0_4.symm
        | exact hu3_4 | exact hu3_4.symm

/- ### Part 7: Long-Edge & xy Twin Lemma (Lemma 4.26) -/

-- Lemma 4.26(a): If μ = false (y present), any twins x', y' of x, y are adjacent.
lemma xy_twin {V : Type} [Fintype V]
    (G : SimpleGraph V) (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} (hi : 2 ≤ i) {ν : Bool} {f : Fin (3 * i - 1) ⊕ Fin 8 → V}
    (hf : ∀ a b,
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => false = true → t.val ≠ 7) a) →
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => false = true → t.val ≠ 7) b) →
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q =>
            i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
            (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ =>
            (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
            (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
            (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
            (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
            (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b) →
      G.Adj (f a) (f b))
    (x' y' : V)
    (hx' : G.Adj x' (f (Sum.inr 0)) ∧ G.Adj x' (f (Sum.inr 4)) ∧ G.Adj x' (f (Sum.inr 2)))
    (hy' : G.Adj y' (f (Sum.inr 3)) ∧ G.Adj y' (f (Sum.inr 1)) ∧ G.Adj y' (f (Sum.inr 5))) :
    G.Adj x' y' := by
  let A : Fin 4 → V := ![x', f (Sum.inr 3), f (Sum.inr 1), f (Sum.inr 5)]
  let B : Fin 4 → V := ![y', f (Sum.inr 0), f (Sum.inr 4), f (Sum.inr 2)]
  have hcube : ∀ r s : Fin 4, r ≠ s → G.Adj (A r) (B s) := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;> dsimp only [A, B, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
      first
      | exact absurd rfl hrs
      | exact hx'.1 | exact hx'.2.1 | exact hx'.2.2
      | exact hy'.1.symm | exact hy'.2.1.symm | exact hy'.2.2.symm
      | exact hf _ _ (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h) (Or.inl (by decide))
  obtain ⟨k, hk⟩ := cube_lemma G hcf hmax hmin A B hcube
  fin_cases k
  · exact hk
  · exfalso; have h := vega_hom_induced hcf hi hf (a := Sum.inr 3) (b := Sum.inr 0) (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h) hk
    dsimp only at h; revert h; decide
  · exfalso; have h := vega_hom_induced hcf hi hf (a := Sum.inr 1) (b := Sum.inr 4) (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h) hk
    dsimp only at h; revert h; decide
  · exfalso; have h := vega_hom_induced hcf hi hf (a := Sum.inr 5) (b := Sum.inr 2) (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h) hk
    dsimp only at h; revert h; decide

-- Lemma 4.26(b): Every long Andrásfai edge p < q (with q - p ≠ i and q - p ≠ 2i - 1,
-- or (p, q) = (0, 2i - 1)) has the twin property directly from the Cube Lemma.
lemma long_edge_twin {V : Type} [Fintype V]
    (G : SimpleGraph V) (hcf : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} (hi : 2 ≤ i) {μ ν : Bool} {f : Fin (3 * i - 1) ⊕ Fin 8 → V}
    (hf : ∀ a b,
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) a) →
      ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) b) →
      ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
        | Sum.inl p, Sum.inl q =>
            i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
            (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inl p, Sum.inr t =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t, Sum.inl p =>
            ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
            ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
            ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
        | Sum.inr t₁, Sum.inr t₂ =>
            (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
            (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
            (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
            (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
            (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b) →
      G.Adj (f a) (f b))
    (p q : Fin (3 * i - 1)) (hpq_lt : p.val < q.val)
    (hdist : i < q.val - p.val ∧ q.val - p.val ≤ 2 * i - 1)
    (hlong : q.val < 2 * i ∨ q.val - p.val < 2 * i - 1)
    (p' q' : V)
    (hp' : ∀ r, ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl s => ν = true → s.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) r) →
      ((fun y : Fin (3 * i - 1) ⊕ Fin 8 => match y with
        | Sum.inl b => i ≤ (b.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧ (b.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inr t => ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨ ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨ ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)) r) →
      G.Adj p' (f r))
    (hq' : ∀ r, ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl s => ν = true → s.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) r) →
      ((fun y : Fin (3 * i - 1) ⊕ Fin 8 => match y with
        | Sum.inl b => i ≤ (b.val + (3 * i - 1) - q.val) % (3 * i - 1) ∧ (b.val + (3 * i - 1) - q.val) % (3 * i - 1) ≤ 2 * i - 1
        | Sum.inr t => ((t.val = 0 ∨ t.val = 3) ∧ q.val < i) ∨ ((t.val = 4 ∨ t.val = 1) ∧ i ≤ q.val ∧ q.val < 2 * i) ∨ ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ q.val)) r) →
      G.Adj q' (f r)) :
    G.Adj p' q' := by
  have hp_lt := p.isLt; have hq_lt := q.isLt
  by_cases hqG : q.val < 2 * i
  · -- Case 1: p < i ≤ q < 2i (Red-Green)
    have hpR : p.val < i := by omega
    have hqG1 : i ≤ q.val := by omega
    let r1 : Fin (3 * i - 1) := ⟨q.val - i, by omega⟩
    let s1 : Fin (3 * i - 1) := ⟨p.val + i, by omega⟩
    have hr1_act : ν = true → r1.val ≠ 2 * i - 1 := fun _ => by simp [r1]; omega
    have hs1_act : ν = true → s1.val ≠ 2 * i - 1 := fun _ => by simp [s1]; omega
    let A : Fin 4 → V := fun x => match x.val with | 0 => p' | 1 => f (Sum.inr 4) | 2 => f (Sum.inr 1) | _ => f (Sum.inl r1)
    let B : Fin 4 → V := fun x => match x.val with | 0 => q' | 1 => f (Sum.inr 0) | 2 => f (Sum.inr 3) | _ => f (Sum.inl s1)
    have hcube : ∀ r s : Fin 4, r ≠ s → G.Adj (A r) (B s) := by
      intro r s hrs
      fin_cases r <;> fin_cases s <;> dsimp only [A, B] <;>
        first
        | exact absurd rfl hrs
        | exact hp' (Sum.inr 0) (by simp) (Or.inl ⟨Or.inl rfl, hpR⟩)
        | exact hp' (Sum.inr 3) (by simp) (Or.inl ⟨Or.inr rfl, hpR⟩)
        | exact hp' (Sum.inl s1) hs1_act (by
            dsimp only
            have : s1.val + (3 * i - 1) - p.val = i + (3 * i - 1) := by simp [s1]; omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
        | exact (hq' (Sum.inr 4) (by simp) (Or.inr (Or.inl ⟨Or.inl rfl, hqG1, hqG⟩))).symm
        | exact (hq' (Sum.inr 1) (by simp) (Or.inr (Or.inl ⟨Or.inr rfl, hqG1, hqG⟩))).symm
        | exact (hq' (Sum.inl r1) hr1_act (by
            dsimp only
            have : r1.val + (3 * i - 1) - q.val = 2 * i - 1 := by simp [r1]; omega
            rw [this, Nat.mod_eq_of_lt (by omega)]; omega)).symm
        | exact hf _ _ (by simp) (by simp) (Or.inl (by decide))
        | exact hf (Sum.inr 4) (Sum.inl s1) (by simp) hs1_act (Or.inr (Or.inl ⟨Or.inl rfl, by dsimp [s1]; omega, by dsimp [s1]; omega⟩))
        | exact hf (Sum.inr 1) (Sum.inl s1) (by simp) hs1_act (Or.inr (Or.inl ⟨Or.inr rfl, by dsimp [s1]; omega, by dsimp [s1]; omega⟩))
        | exact hf (Sum.inl r1) (Sum.inr 0) hr1_act (by simp) (Or.inl ⟨Or.inl rfl, by dsimp [r1]; omega⟩)
        | exact hf (Sum.inl r1) (Sum.inr 3) hr1_act (by simp) (Or.inl ⟨Or.inr rfl, by dsimp [r1]; omega⟩)
    obtain ⟨k, hk⟩ := cube_lemma G hcf hmax hmin A B hcube
    fin_cases k
    · exact hk
    · exfalso; have h := vega_hom_induced hcf hi hf (a := Sum.inr 4) (b := Sum.inr 0) (by simp) (by simp) hk
      dsimp only at h; revert h; decide
    · exfalso; have h := vega_hom_induced hcf hi hf (a := Sum.inr 1) (b := Sum.inr 3) (by simp) (by simp) hk
      dsimp only at h; revert h; decide
    · exfalso
      have hbad := vega_hom_induced hcf hi hf (a := Sum.inl r1) (b := Sum.inl s1) hr1_act hs1_act hk
      dsimp only at hbad
      have heq : s1.val + (3 * i - 1) - r1.val = (2 * i - (q.val - p.val)) + (3 * i - 1) := by
        simp [r1, s1]; omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hbad
      omega
  · by_cases hpR : p.val < i
    · -- Case 2: p < i, 2i ≤ q, q - p < 2i - 1 (Red-Blue long edge)
      have hlt2 : q.val - p.val < 2 * i - 1 := hlong.resolve_left hqG
      let r1 : Fin (3 * i - 1) := ⟨q.val + 1 - 2 * i, by omega⟩
      let s1 : Fin (3 * i - 1) := ⟨p.val + 2 * i - 1, by omega⟩
      have hr1_act : ν = true → r1.val ≠ 2 * i - 1 := fun _ => by simp [r1]; omega
      have hs1_act : ν = true → s1.val ≠ 2 * i - 1 := fun _ => by simp [s1]; omega
      let A : Fin 4 → V := fun x => match x.val with | 0 => p' | 1 => f (Sum.inr 2) | 2 => f (Sum.inr 5) | _ => f (Sum.inl r1)
      let B : Fin 4 → V := fun x => match x.val with | 0 => q' | 1 => f (Sum.inr 0) | 2 => f (Sum.inr 3) | _ => f (Sum.inl s1)
      have hcube : ∀ r s : Fin 4, r ≠ s → G.Adj (A r) (B s) := by
        intro r s hrs
        fin_cases r <;> fin_cases s <;> dsimp only [A, B] <;>
          first
          | exact absurd rfl hrs
          | exact hp' (Sum.inr 0) (by simp) (Or.inl ⟨Or.inl rfl, hpR⟩)
          | exact hp' (Sum.inr 3) (by simp) (Or.inl ⟨Or.inr rfl, hpR⟩)
          | exact hp' (Sum.inl s1) hs1_act (by
              dsimp only
              have : s1.val + (3 * i - 1) - p.val = (2 * i - 1) + (3 * i - 1) := by simp [s1]; omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
          | exact (hq' (Sum.inr 2) (by simp) (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩))).symm
          | exact (hq' (Sum.inr 5) (by simp) (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩))).symm
          | exact (hq' (Sum.inl r1) hr1_act (by
              dsimp only
              have : r1.val + (3 * i - 1) - q.val = i := by simp [r1]; omega
              rw [this, Nat.mod_eq_of_lt (by omega)]; omega)).symm
          | exact hf _ _ (by simp) (by simp) (Or.inl (by decide))
          | exact hf (Sum.inr 2) (Sum.inl s1) (by simp) hs1_act (Or.inr (Or.inr ⟨Or.inl rfl, by simp [s1]; omega⟩))
          | exact hf (Sum.inr 5) (Sum.inl s1) (by simp) hs1_act (Or.inr (Or.inr ⟨Or.inr rfl, by simp [s1]; omega⟩))
          | exact hf (Sum.inl r1) (Sum.inr 0) hr1_act (by simp) (Or.inl ⟨Or.inl rfl, by simp [r1]; omega⟩)
          | exact hf (Sum.inl r1) (Sum.inr 3) hr1_act (by simp) (Or.inl ⟨Or.inr rfl, by simp [r1]; omega⟩)
      obtain ⟨k, hk⟩ := cube_lemma G hcf hmax hmin A B hcube
      fin_cases k
      · exact hk
      · exfalso; have h := vega_hom_induced hcf hi hf (a := Sum.inr 2) (b := Sum.inr 0) (by simp) (by simp) hk
        dsimp only at h; revert h; decide
      · exfalso; have h := vega_hom_induced hcf hi hf (a := Sum.inr 5) (b := Sum.inr 3) (by simp) (by simp) hk
        dsimp only at h; revert h; decide
      · exfalso
        have hbad := vega_hom_induced hcf hi hf (a := Sum.inl r1) (b := Sum.inl s1) hr1_act hs1_act hk
        dsimp only at hbad
        have heq : s1.val + (3 * i - 1) - r1.val = (4 * i - 2 - (q.val - p.val)) + (3 * i - 1) := by
          simp [r1, s1]; omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hbad
        omega
    · -- Case 3: i ≤ p < 2i ≤ q (Green-Blue long edge)
      have hpG : i ≤ p.val ∧ p.val < 2 * i := ⟨by omega, by omega⟩
      let r1 : Fin (3 * i - 1) := ⟨q.val - i, by omega⟩
      let s1 : Fin (3 * i - 1) := ⟨p.val + i, by omega⟩
      have hr1_act : ν = true → r1.val ≠ 2 * i - 1 := fun _ => by simp [r1]; omega
      have hs1_act : ν = true → s1.val ≠ 2 * i - 1 := fun _ => by simp [s1]; omega
      let A : Fin 4 → V := fun x => match x.val with | 0 => p' | 1 => f (Sum.inr 2) | 2 => f (Sum.inr 5) | _ => f (Sum.inl r1)
      let B : Fin 4 → V := fun x => match x.val with | 0 => q' | 1 => f (Sum.inr 4) | 2 => f (Sum.inr 1) | _ => f (Sum.inl s1)
      have hcube : ∀ r s : Fin 4, r ≠ s → G.Adj (A r) (B s) := by
        intro r s hrs
        fin_cases r <;> fin_cases s <;> dsimp only [A, B] <;>
          first
          | exact absurd rfl hrs
          | exact hp' (Sum.inr 4) (by simp) (Or.inr (Or.inl ⟨Or.inl rfl, hpG⟩))
          | exact hp' (Sum.inr 1) (by simp) (Or.inr (Or.inl ⟨Or.inr rfl, hpG⟩))
          | exact hp' (Sum.inl s1) hs1_act (by
              dsimp only
              have : s1.val + (3 * i - 1) - p.val = i + (3 * i - 1) := by simp [s1]; omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega)
          | exact (hq' (Sum.inr 2) (by simp) (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩))).symm
          | exact (hq' (Sum.inr 5) (by simp) (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩))).symm
          | exact (hq' (Sum.inl r1) hr1_act (by
              dsimp only
              have : r1.val + (3 * i - 1) - q.val = 2 * i - 1 := by simp [r1]; omega
              rw [this, Nat.mod_eq_of_lt (by omega)]; omega)).symm
          | exact hf _ _ (by simp) (by simp) (Or.inl (by decide))
          | exact hf (Sum.inr 2) (Sum.inl s1) (by simp) hs1_act (Or.inr (Or.inr ⟨Or.inl rfl, by simp [s1]; omega⟩))
          | exact hf (Sum.inr 5) (Sum.inl s1) (by simp) hs1_act (Or.inr (Or.inr ⟨Or.inr rfl, by simp [s1]; omega⟩))
          | exact hf (Sum.inl r1) (Sum.inr 4) hr1_act (by simp) (Or.inr (Or.inl ⟨Or.inl rfl, by simp [r1]; omega, by simp [r1]; omega⟩))
          | exact hf (Sum.inl r1) (Sum.inr 1) hr1_act (by simp) (Or.inr (Or.inl ⟨Or.inr rfl, by simp [r1]; omega, by simp [r1]; omega⟩))
      obtain ⟨k, hk⟩ := cube_lemma G hcf hmax hmin A B hcube
      fin_cases k
      · exact hk
      · exfalso; have h := vega_hom_induced hcf hi hf (a := Sum.inr 2) (b := Sum.inr 4) (by simp) (by simp) hk
        dsimp only at h; revert h; decide
      · exfalso; have h := vega_hom_induced hcf hi hf (a := Sum.inr 5) (b := Sum.inr 1) (by simp) (by simp) hk
        dsimp only at h; revert h; decide
      · exfalso
        have hbad := vega_hom_induced hcf hi hf (a := Sum.inl r1) (b := Sum.inl s1) hr1_act hs1_act hk
        dsimp only at hbad
        have heq : s1.val + (3 * i - 1) - r1.val = (2 * i - (q.val - p.val)) + (3 * i - 1) := by
          simp [r1, s1]; omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hbad
        omega

/- ### Part 8: Main Reduction Theorem -/

theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R2_H2_R2.H1 := by
  intro h1 h2
  classical
  intro V _ G _ hcf hmax hmin _ ⟨v, u, w, hg⟩
  -- Step 1: Embed Grötzsch as Υ_2^{11} (order 11)
  obtain ⟨f0, hf0⟩ := grotzsch_to_vega211 v u w hg
  -- Step 2: Select a maximum-order Vega subgraph Υ_i^{μν} ⊆ G
  let P : ℕ → Prop := fun m =>
    ∃ (i : ℕ) (μ ν : Bool) (f : Fin (3 * i - 1) ⊕ Fin 8 → V),
      2 ≤ i ∧ 3 * i + 7 - μ.toNat - ν.toNat = m ∧
      ∀ a b,
        ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) a) →
        ((fun x : Fin (3 * i - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν = true → p.val ≠ 2 * i - 1 | Sum.inr t => μ = true → t.val ≠ 7) b) →
        ((fun x y : Fin (3 * i - 1) ⊕ Fin 8 => match x, y with
          | Sum.inl p, Sum.inl q =>
              i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
              (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
          | Sum.inl p, Sum.inr t =>
              ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
              ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
              ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
          | Sum.inr t, Sum.inl p =>
              ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
              ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
              ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
          | Sum.inr t₁, Sum.inr t₂ =>
              (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
              (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
              (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
              (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
              (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b) →
        G.Adj (f a) (f b)
  let S : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter P
  have hS_ne : S.Nonempty := by
    refine ⟨11, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, 2, true, true, f0, le_refl 2, rfl,
      fun a b ha hb h => by cases a <;> cases b <;> exact hf0 _ _ ha hb h⟩⟩
    have hle := vega_card_le (μ := true) (ν := true) hcf (le_refl 2)
      (fun a b ha hb h => by cases a <;> cases b <;> exact hf0 _ _ ha hb h)
    simp at hle; omega
  let m0 := S.max' hS_ne
  have hm0_mem : m0 ∈ S := Finset.max'_mem S hS_ne
  obtain ⟨i, μ, ν, f, hi, hord, hf⟩ := (Finset.mem_filter.mp hm0_mem).2
  have hmax_vega : ∀ (i' : ℕ) (μ' ν' : Bool) (f' : Fin (3 * i' - 1) ⊕ Fin 8 → V), 2 ≤ i' →
      (∀ a b,
        ((fun x : Fin (3 * i' - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν' = true → p.val ≠ 2 * i' - 1 | Sum.inr t => μ' = true → t.val ≠ 7) a) →
        ((fun x : Fin (3 * i' - 1) ⊕ Fin 8 => match x with | Sum.inl p => ν' = true → p.val ≠ 2 * i' - 1 | Sum.inr t => μ' = true → t.val ≠ 7) b) →
        ((fun x y : Fin (3 * i' - 1) ⊕ Fin 8 => match x, y with
          | Sum.inl p, Sum.inl q =>
              i' ≤ (q.val + (3 * i' - 1) - p.val) % (3 * i' - 1) ∧
              (q.val + (3 * i' - 1) - p.val) % (3 * i' - 1) ≤ 2 * i' - 1
          | Sum.inl p, Sum.inr t =>
              ((t.val = 0 ∨ t.val = 3) ∧ p.val < i') ∨
              ((t.val = 4 ∨ t.val = 1) ∧ i' ≤ p.val ∧ p.val < 2 * i') ∨
              ((t.val = 2 ∨ t.val = 5) ∧ 2 * i' ≤ p.val)
          | Sum.inr t, Sum.inl p =>
              ((t.val = 0 ∨ t.val = 3) ∧ p.val < i') ∨
              ((t.val = 4 ∨ t.val = 1) ∧ i' ≤ p.val ∧ p.val < 2 * i') ∨
              ((t.val = 2 ∨ t.val = 5) ∧ 2 * i' ≤ p.val)
          | Sum.inr t₁, Sum.inr t₂ =>
              (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
              (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
              (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
              (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
              (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) a b) →
        G.Adj (f' a) (f' b)) →
      3 * i' + 7 - μ'.toNat - ν'.toNat ≤ 3 * i + 7 - μ.toNat - ν.toNat := by
    intro i' μ' ν' f' hi' hf'
    rw [hord]
    have hmem : 3 * i' + 7 - μ'.toNat - ν'.toNat ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, i', μ', ν', f', hi', rfl, hf'⟩
      have hle := vega_card_le hcf hi' hf'
      omega
    exact Finset.le_max' S _ hmem
  -- Step 3: Apply H1 (Vega Twin Lemma) and H2 (Vega Attachment Lemma)
  have htwin := h1 V G hcf hmax hmin i μ ν f hi hf hmax_vega
  have hattach := h2 V G hcf hmax hmin i μ ν f hi hf hmax_vega htwin
  -- Step 4: Choose twin map φ : V → V(Υ_i^{μν}) ⊆ V(Υ_i^{00}) and verify homomorphism
  choose φ hφ_act hφ_twin using hattach
  refine ⟨i, hi, φ, fun x y hxy => ?_⟩
  by_contra hnadj
  by_cases hfeq : φ x = φ y
  · obtain ⟨r, hr_act, hr_adj⟩ := vega_has_neighbor hi μ ν (φ x)
    have hx_r : G.Adj x (f r) := hφ_twin x r hr_act hr_adj
    have hy_r : G.Adj y (f r) := hφ_twin y r hr_act (hfeq ▸ hr_adj)
    exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf hx_r.symm hy_r.symm hxy
  · obtain ⟨r, hr_act, hxr_adj, hyr_adj⟩ :=
      vega_maximal_tf hi μ ν (φ x) (φ y) (hφ_act x) (hφ_act y) hfeq hnadj
    have hx_r : G.Adj x (f r) := hφ_twin x r hr_act hxr_adj
    have hy_r : G.Adj y (f r) := hφ_twin y r hr_act hyr_adj
    exact OMA.R_Erdos128_erdos_128_R2_H2_R2.not_adj_both hcf hx_r.symm hy_r.symm hxy

end OMA.R_Erdos128_erdos_128_R2_H2_R2_H1_R1
