import OMAReductions.R_Erdos64_erdos_64_R1
import Mathlib

/-!
# The equality case of the noncubic step

Step H2 of reduction Erdos64.erdos_64.R1 (PR 466) concerns graphs of minimum degree three
with a vertex of degree at least four, in which the vertices of degree at least four are
independent and every vertex has a cubic neighbour (Markström's structure of a minimal
counterexample). Double counting the edges between the cubic vertices and the others gives
n3 ≥ 2 n4. This reduction disposes of the 4-cycle case and of the equality case n3 = 2 n4:
there every vertex of degree at least four has degree exactly four, and every cubic vertex has
exactly two such neighbours, so replacing each cubic vertex by an edge yields a simple
4-regular graph on the vertices of degree four. A cycle of length 2^k there lifts to a cycle
of length 2^(k+1) through the subdivision vertices. What remains is

* H1: the step itself with no 4-cycle and strictly more than two thirds of the vertices cubic;
* H2: every finite 4-regular graph without 4-cycles has a cycle of length 2^k.

The equality argument is the one used for the strict two-thirds bound on minimal
counterexamples (erdosproblems.com/64 forum, 26 July 2026; Ducoffe and Dumitru,
arXiv:2609.28594), here made unconditional, without any minimality assumption.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H2_R2

open SimpleGraph Finset

/-- The noncubic case without 4-cycles and with strictly more than two thirds
of the vertices cubic. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree → (∃ v, 3 < G.degree v) →
    (∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
    (∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3) →
    (∀ a x b y, G.Adj a x → G.Adj x b → G.Adj b y → G.Adj y a → a = b ∨ x = y) →
    2 * Fintype.card V < 3 * (univ.filter (fun x => G.degree x = 3)).card →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- Four-regular graphs without 4-cycles. -/
def H2 : Prop :=
  ∀ (W : Type) (H : SimpleGraph W) [Fintype W] [DecidableRel H.Adj],
    Nonempty W → (∀ v, H.degree v = 4) →
    (∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ H

/-- A periodic sequence of consecutive adjacent vertices, injective on one period,
spans a copy of the cycle graph. -/
theorem copy_of_periodic {X : Type} (K : SimpleGraph X) (N : ℕ) (hN : 2 ≤ N) (d : ℕ → X)
    (hper : ∀ n, d (n + N) = d n) (hadj : ∀ n, K.Adj (d n) (d (n + 1)))
    (hinj : ∀ a b, a < N → b < N → d a = d b → a = b) : cycleGraph N ⊑ K := by
  have step : ∀ t t' : Fin N, (t' - t).val = 1 → K.Adj (d t.val) (d t'.val) := by
    intro t t' h
    rw [Fin.val_sub] at h
    have ht := t.isLt
    have ht' := t'.isLt
    by_cases hs : N - t.val + t'.val < N
    · rw [Nat.mod_eq_of_lt hs] at h
      have h0 : t'.val = 0 := by omega
      have h1 : t.val + 1 = N := by omega
      have e : d t'.val = d (t.val + 1) := by rw [h0, h1, ← hper 0, Nat.zero_add]
      rw [e]
      exact hadj _
    · have hs2 : N - t.val + t'.val - N < N := by omega
      rw [Nat.mod_eq_sub_mod (show N - t.val + t'.val ≥ N by omega), Nat.mod_eq_of_lt hs2] at h
      have h1 : t'.val = t.val + 1 := by omega
      rw [h1]
      exact hadj _
  refine ⟨⟨⟨fun t => d t.val, ?_⟩, ?_⟩⟩
  · intro t t' h
    rw [cycleGraph_adj'] at h
    rcases h with h | h
    · exact (step t' t h).symm
    · exact step t t' h
  · intro t t' h
    change d t.val = d t'.val at h
    exact Fin.ext (hinj _ _ t.isLt t'.isLt h)

/-- A copy of a cycle graph gives a periodic sequence of consecutive adjacent vertices. -/
theorem seq_of_copy {X : Type} (K : SimpleGraph X) (N : ℕ) (hN : 2 ≤ N) (h : cycleGraph N ⊑ K) :
    ∃ c : ℕ → X, (∀ n, c (n + N) = c n) ∧ (∀ n, K.Adj (c n) (c (n + 1))) ∧
      (∀ a b, a < N → b < N → c a = c b → a = b) := by
  obtain ⟨f⟩ := h
  have hpos : 0 < N := by omega
  refine ⟨fun n => f.toHom ⟨n % N, Nat.mod_lt _ hpos⟩, ?_, ?_, ?_⟩
  · intro n
    simp only [Nat.add_mod_right]
  · intro n
    apply f.toHom.map_adj
    rw [cycleGraph_adj']
    right
    show (N - n % N + (n + 1) % N) % N = 1
    have hr := Nat.mod_lt n hpos
    have h1N : 1 < N := by omega
    have e1 : (n + 1) % N = (n % N + 1) % N := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt h1N]
    rw [e1]
    rcases Nat.lt_or_ge (n % N + 1) N with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt, show N - n % N + (n % N + 1) = N + 1 by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt h1N]
    · have he : n % N + 1 = N := by omega
      rw [he, Nat.mod_self, Nat.add_zero, show N - n % N = 1 by omega, Nat.mod_eq_of_lt h1N]
  · intro a b ha hb hab
    have := f.injective' hab
    rw [Fin.mk.injEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact this

/-- A 4-cycle given by its vertices. -/
theorem copy_four {X : Type} (K : SimpleGraph X) (a x b y : X) (h1 : K.Adj a x) (h2 : K.Adj x b)
    (h3 : K.Adj b y) (h4 : K.Adj y a) (hab : a ≠ b) (hxy : x ≠ y) : cycleGraph 4 ⊑ K := by
  have n1 := K.ne_of_adj h1
  have n2 := K.ne_of_adj h2
  have n3 := K.ne_of_adj h3
  have n4 := K.ne_of_adj h4
  apply copy_of_periodic K 4 (by norm_num)
    (fun n => if n % 4 = 0 then a else if n % 4 = 1 then x else if n % 4 = 2 then b else y)
  · intro n
    simp only [Nat.add_mod_right]
  · intro n
    have e : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
    obtain h | h | h | h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    all_goals simp [e, h, h1, h2, h3, h4]
  · intro i j hi hj hij
    interval_cases i <;> interval_cases j <;> simp at hij ⊢ <;> simp_all [eq_comm]

/-- A cycle of length m in a graph whose edges are replaced by internally disjoint
paths of length two gives a cycle of length 2m. -/
theorem lift_double {X Y : Type} (G : SimpleGraph X) (H : SimpleGraph Y) (emb : Y → X)
    (emb_inj : Function.Injective emb) (mid : Y → Y → X)
    (hmid : ∀ v w, H.Adj v w → G.Adj (emb v) (mid v w) ∧ G.Adj (mid v w) (emb w))
    (hne : ∀ v w z, H.Adj v w → mid v w ≠ emb z)
    (hsame : ∀ v w v' w', H.Adj v w → H.Adj v' w' → mid v w = mid v' w' →
      v' = v ∨ v' = w)
    (m : ℕ) (hm : 3 ≤ m) (h : cycleGraph m ⊑ H) : cycleGraph (2 * m) ⊑ G := by
  obtain ⟨c, hper, hadj, hinj⟩ := seq_of_copy H m (by omega) h
  have succ_eq : ∀ i, i < m → c (i + 1) = c (if i + 1 < m then i + 1 else 0) := by
    intro i hi
    by_cases h' : i + 1 < m
    · rw [if_pos h']
    · rw [if_neg h', show i + 1 = 0 + m by omega, hper]
  apply copy_of_periodic G (2 * m) (by omega)
    (fun n => if n % 2 = 0 then emb (c (n / 2)) else mid (c (n / 2)) (c (n / 2 + 1)))
  · intro n
    try simp only
    rw [show (n + 2 * m) % 2 = n % 2 by omega, show (n + 2 * m) / 2 = n / 2 + m by omega, hper,
      show n / 2 + m + 1 = (n / 2 + 1) + m by omega, hper]
  · intro n
    try simp only
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h0
    · rw [if_pos h0, if_neg (show ¬ (n + 1) % 2 = 0 by omega), show (n + 1) / 2 = n / 2 by omega]
      exact (hmid _ _ (hadj _)).1
    · rw [if_neg (show ¬ n % 2 = 0 by omega), if_pos (show (n + 1) % 2 = 0 by omega),
        show (n + 1) / 2 = n / 2 + 1 by omega]
      exact (hmid _ _ (hadj _)).2
  · intro a b ha hb hab
    try simp only at hab
    have ha2 : a / 2 < m := by omega
    have hb2 : b / 2 < m := by omega
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h0 <;>
      rcases Nat.mod_two_eq_zero_or_one b with h1 | h1
    · rw [if_pos h0, if_pos h1] at hab
      have := hinj _ _ ha2 hb2 (emb_inj hab)
      omega
    · rw [if_pos h0, if_neg (show ¬ b % 2 = 0 by omega)] at hab
      exact absurd hab.symm (hne _ _ _ (hadj _))
    · rw [if_neg (show ¬ a % 2 = 0 by omega), if_pos h1] at hab
      exact absurd hab (hne _ _ _ (hadj _))
    · rw [if_neg (show ¬ a % 2 = 0 by omega), if_neg (show ¬ b % 2 = 0 by omega)] at hab
      rcases hsame _ _ _ _ (hadj (a / 2)) (hadj (b / 2)) hab with s1 | s1
      · have := hinj _ _ hb2 ha2 s1
        omega
      · rcases hsame _ _ _ _ (hadj (b / 2)) (hadj (a / 2)) hab.symm with s2 | s2
        · have := hinj _ _ ha2 hb2 s2
          omega
        · rw [succ_eq _ ha2] at s1
          rw [succ_eq _ hb2] at s2
          have hq : b / 2 = (if a / 2 + 1 < m then a / 2 + 1 else 0) :=
            hinj _ _ hb2 (by split_ifs <;> omega) s1
          have hp : a / 2 = (if b / 2 + 1 < m then b / 2 + 1 else 0) :=
            hinj _ _ ha2 (by split_ifs <;> omega) s2
          split_ifs at hq hp <;> omega

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1.H2 := by
  intro h1 h2 V G _ _ hmin hbig hedge hdom
  have finish : ∀ k, 2 ≤ k → cycleGraph (2 ^ k) ⊑ G →
      ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
    intro k hk hc
    have h4 : 4 ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    obtain ⟨v, c, hc1, hc2⟩ := (cycleGraph_isContained_iff (by omega)).mp hc
    exact ⟨k, v, c, hk, hc1, hc2⟩
  -- a 4-cycle
  classical
  by_cases hc4 : ∀ a x b y, G.Adj a x → G.Adj x b → G.Adj b y → G.Adj y a → a = b ∨ x = y
  swap
  · push_neg at hc4
    obtain ⟨a, x, b, y, h1, h2, h3, h4, hab, hxy⟩ := hc4
    exact finish 2 le_rfl (copy_four G a x b y h1 h2 h3 h4 hab hxy)
  -- strictly more than two thirds cubic
  by_cases hst : 2 * Fintype.card V < 3 * (univ.filter (fun x => G.degree x = 3)).card
  · exact h1 V G hmin hbig hedge hdom hc4 hst
  push_neg at hst
  -- the equality case
  have deg_ge : ∀ u, 3 ≤ G.degree u := fun u => le_trans hmin (G.minDegree_le_degree u)
  have indep : ∀ u v, G.Adj u v → G.degree u ≠ 3 → G.degree v = 3 := by
    intro u v huv hu
    rcases hedge huv with h | h
    · exact absurd h hu
    · exact h
  set S3 := univ.filter (fun x => G.degree x = 3) with hS3
  set S4 := univ.filter (fun x => ¬ G.degree x = 3) with hS4
  have mem3 : ∀ x, x ∈ S3 ↔ G.degree x = 3 := by intro x; simp [hS3]
  have mem4 : ∀ x, x ∈ S4 ↔ G.degree x ≠ 3 := by intro x; simp [hS4]
  have hcardV : S3.card + S4.card = Fintype.card V := by
    rw [hS3, hS4, ← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not (fun x => G.degree x = 3)
  have deg4 : ∀ u ∈ S4, G.degree u = (S3.bipartiteAbove G.Adj u).card := by
    intro u hu
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext x
    rw [Finset.mem_bipartiteAbove, mem_neighborFinset, mem3]
    constructor
    · intro h
      exact ⟨indep u x h ((mem4 u).mp hu), h⟩
    · intro h
      exact h.2
  have deg3 : ∀ x ∈ S3, (S4.bipartiteBelow G.Adj x).card ≤ 2 := by
    intro x hx
    obtain ⟨b, hxb, hb⟩ := hdom x
    have hsub : S4.bipartiteBelow G.Adj x ⊆ (G.neighborFinset x).erase b := by
      intro u hu
      rw [Finset.mem_bipartiteBelow, mem4] at hu
      rw [Finset.mem_erase, mem_neighborFinset]
      exact ⟨fun h => hu.1 (by rw [h]; exact hb), hu.2.symm⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset x b).mpr hxb),
      G.card_neighborFinset_eq_degree, (mem3 x).mp hx] at this
    omega
  have dc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := G.Adj) (s := S4)
    (t := S3)
  have sumA : ∑ u ∈ S4, G.degree u = ∑ x ∈ S3, (S4.bipartiteBelow G.Adj x).card := by
    rw [← dc]
    exact Finset.sum_congr rfl deg4
  have up : ∑ x ∈ S3, (S4.bipartiteBelow G.Adj x).card ≤ 2 * S3.card := by
    calc _ ≤ ∑ x ∈ S3, 2 := Finset.sum_le_sum deg3
      _ = 2 * S3.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have low : 4 * S4.card ≤ ∑ u ∈ S4, G.degree u := by
    calc 4 * S4.card = ∑ u ∈ S4, 4 := by rw [Finset.sum_const, smul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun u hu => by
          have := deg_ge u
          have := (mem4 u).mp hu
          omega)
  have eq4 : ∀ u ∈ S4, G.degree u = 4 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨u, hu, hne⟩ := hcon
    have hlt : ∑ v ∈ S4, 4 < ∑ v ∈ S4, G.degree v :=
      Finset.sum_lt_sum (fun v hv => by
          have := deg_ge v
          have := (mem4 v).mp hv
          omega)
        ⟨u, hu, by
          have := deg_ge u
          have := (mem4 u).mp hu
          omega⟩
    rw [Finset.sum_const, smul_eq_mul] at hlt
    omega
  have eq2 : ∀ x ∈ S3, (S4.bipartiteBelow G.Adj x).card = 2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, hx, hne⟩ := hcon
    have hlt : ∑ y ∈ S3, (S4.bipartiteBelow G.Adj y).card < ∑ y ∈ S3, 2 :=
      Finset.sum_lt_sum deg3 ⟨x, hx, by have := deg3 x hx; omega⟩
    rw [Finset.sum_const, smul_eq_mul] at hlt
    omega
  have two : ∀ x, G.degree x = 3 → ∀ a b c, G.degree a ≠ 3 → G.degree b ≠ 3 →
      G.degree c ≠ 3 → G.Adj a x → G.Adj b x → G.Adj c x → a ≠ b → c = a ∨ c = b := by
    intro x hx a b c ha hb hc hax hbx hcx hab
    by_contra hcon
    push_neg at hcon
    have hmem : ∀ w, G.degree w ≠ 3 → G.Adj w x → w ∈ S4.bipartiteBelow G.Adj x := by
      intro w hw hwx
      rw [Finset.mem_bipartiteBelow, mem4]
      exact ⟨hw, hwx⟩
    have h3 : 2 < (S4.bipartiteBelow G.Adj x).card :=
      Finset.two_lt_card.mpr ⟨a, hmem a ha hax, b, hmem b hb hbx, c, hmem c hc hcx, hab,
        fun h => hcon.1 h.symm, fun h => hcon.2 h.symm⟩
    have := eq2 x ((mem3 x).mpr hx)
    omega
  -- the four-regular graph on the vertices of degree at least four
  obtain ⟨H, hH⟩ : ∃ H : SimpleGraph {u : V // G.degree u ≠ 3}, ∀ u v,
      H.Adj u v ↔ (u ≠ v ∧ ∃ x, G.Adj u.1 x ∧ G.Adj x v.1) := by
    refine ⟨{ Adj := fun u v => (u ≠ v ∧ ∃ x, G.Adj u.1 x ∧ G.Adj x v.1)
              symm := ⟨fun u v h => ⟨h.1.symm, h.2.choose, h.2.choose_spec.2.symm,
                h.2.choose_spec.1.symm⟩⟩
              loopless := ⟨fun u h => h.1 rfl⟩ }, fun _ _ => Iff.rfl⟩
  haveI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have exmid : ∀ v w : {u : V // G.degree u ≠ 3}, ∃ x : V,
      H.Adj v w → G.Adj v.1 x ∧ G.Adj x w.1 := by
    intro v w
    by_cases h : H.Adj v w
    · obtain ⟨-, x, h1, h2⟩ := (hH v w).mp h
      exact ⟨x, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨v.1, fun h' => absurd h' h⟩
  choose mid hmid using exmid
  have lift : ∀ m, 3 ≤ m → cycleGraph m ⊑ H → cycleGraph (2 * m) ⊑ G := by
    intro m hm hcyc
    refine lift_double G H Subtype.val Subtype.val_injective mid hmid ?_ ?_ m hm hcyc
    · intro v w z hvw heq
      have h3 : G.degree (mid v w) = 3 := indep _ _ (hmid v w hvw).1 v.2
      exact z.2 (by rw [← heq]; exact h3)
    · intro v w v' w' hvw hvw' heq
      have hx : G.degree (mid v w) = 3 := indep _ _ (hmid v w hvw).1 v.2
      have hne : v.1 ≠ w.1 := fun h => ((hH v w).mp hvw).1 (Subtype.ext h)
      have hv'x : G.Adj v'.1 (mid v w) := by rw [heq]; exact (hmid v' w' hvw').1
      exact (two _ hx _ _ _ v.2 w.2 v'.2 (hmid v w hvw).1 (hmid v w hvw).2.symm hv'x
        hne).imp Subtype.ext Subtype.ext
  have hdegH : ∀ u, H.degree u = 4 := by
    intro u
    have hu4 : G.degree u.1 = 4 := eq4 u.1 ((mem4 u.1).mpr u.2)
    apply le_antisymm
    · rw [← card_neighborFinset_eq_degree, ← hu4, ← card_neighborFinset_eq_degree]
      apply Finset.card_le_card_of_injOn (fun v => mid u v)
      · intro v hv
        simp only [Finset.mem_coe, mem_neighborFinset] at hv ⊢
        exact (hmid u v hv).1
      · intro v hv v' hv' heq
        simp only [Finset.mem_coe, mem_neighborFinset] at hv hv'
        have heq' : mid u v = mid u v' := heq
        have hx : G.degree (mid u v) = 3 := indep _ _ (hmid u v hv).1 u.2
        have hne : u.1 ≠ v.1 := fun h => ((hH u v).mp hv).1 (Subtype.ext h)
        have hv'x : G.Adj v'.1 (mid u v) := by rw [heq']; exact (hmid u v' hv').2.symm
        rcases two _ hx _ _ _ u.2 v.2 v'.2 (hmid u v hv).1 (hmid u v hv).2.symm hv'x hne with
          h | h
        · exact absurd (Subtype.ext h).symm ((hH u v').mp hv').1
        · exact (Subtype.ext h).symm
    · have exo : ∀ x : V, ∃ v : {u : V // G.degree u ≠ 3},
          G.Adj u.1 x → (v ≠ u ∧ G.Adj x v.1) := by
        intro x
        by_cases hx : G.Adj u.1 x
        · have hx3 : G.degree x = 3 := indep _ _ hx u.2
          have hc := eq2 x ((mem3 x).mpr hx3)
          obtain ⟨p, hp, q, hq, hpq⟩ :=
            Finset.one_lt_card.mp (by omega : 1 < (S4.bipartiteBelow G.Adj x).card)
          rw [Finset.mem_bipartiteBelow, mem4] at hp hq
          by_cases hpu : p = u.1
          · refine ⟨⟨q, hq.1⟩, fun _ => ⟨fun h => hpq ?_, hq.2.symm⟩⟩
            rw [hpu]
            exact (congrArg Subtype.val h).symm
          · exact ⟨⟨p, hp.1⟩, fun _ => ⟨fun h => hpu (congrArg Subtype.val h), hp.2.symm⟩⟩
        · exact ⟨u, fun h => absurd h hx⟩
      choose o ho using exo
      rw [← card_neighborFinset_eq_degree, ← hu4, ← card_neighborFinset_eq_degree]
      apply Finset.card_le_card_of_injOn o
      · intro x hx
        simp only [Finset.mem_coe, mem_neighborFinset] at hx ⊢
        rw [hH]
        exact ⟨(ho x hx).1.symm, x, hx, (ho x hx).2⟩
      · intro x hx x' hx' heq
        simp only [Finset.mem_coe, mem_neighborFinset] at hx hx'
        by_contra hxx
        have hvu : u.1 ≠ (o x).1 := fun h => (ho x hx).1 (Subtype.ext h).symm
        have heq' : o x = o x' := heq
        have hx'o : G.Adj (o x).1 x' := by rw [heq']; exact (ho x' hx').2.symm
        rcases hc4 u.1 x (o x).1 x' hx (ho x hx).2 hx'o hx'.symm with h | h
        · exact hvu h
        · exact hxx h
  obtain ⟨v0, hv0⟩ := hbig
  have hne : Nonempty {u : V // G.degree u ≠ 3} := ⟨⟨v0, by omega⟩⟩
  by_cases hc4H : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y
  · obtain ⟨k, hk, hcyc⟩ := h2 _ H hne hdegH hc4H
    have h4 : 4 ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hl := lift (2 ^ k) (by omega) hcyc
    refine finish (k + 1) (by omega) ?_
    rw [pow_succ, mul_comm]
    exact hl
  · push_neg at hc4H
    obtain ⟨a, x, b, y, h1, h2, h3, h4, hab, hxy⟩ := hc4H
    exact finish 3 (by norm_num) (lift 4 (by norm_num) (copy_four H a x b y h1 h2 h3 h4 hab hxy))

end OMA.R_Erdos64_erdos_64_R1_H2_R2
