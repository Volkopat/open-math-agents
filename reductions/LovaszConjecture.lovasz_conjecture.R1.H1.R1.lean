import OMAReductions.R_LovaszConjecture_lovasz_conjecture_R1
import Mathlib

/-!
# Lovász's conjecture for order `pq`: the order `p²` case and every abelian Cayley graph

Reduction `LovaszConjecture.lovasz_conjecture.R1.H1.R1` of the step
`LovaszConjecture.lovasz_conjecture.R1.H1` (connected vertex-transitive graphs of order `p * q`,
`p`, `q` prime).

Proved here, with no extra hypotheses:
* `ham_of_comm` (zigzag lemma): a connected graph on which a finite abelian group acts
  transitively by automorphisms has a Hamiltonian path. Induction over the connection set
  `s₁, …, sₖ`: if `L` lists the orbit of `H = ⟨s₁, …, sᵢ⟩` along edges, with `m` least such that
  `sᵐ v₀` lies in that orbit, then `L, s L⁻¹, s² L, s³ L⁻¹, …, sᵐ⁻¹ L^±` lists the orbit of
  `⟨H, s⟩` (consecutive blocks are joined by an `s`-edge, using commutativity).
* `ham_of_card_sq` (order `p²`): a Sylow `p`-subgroup `P` of the automorphism group is transitive
  (index count); a central element `z ≠ 1` of `P` has no fixed point; with `g ∈ P` sending `v₀`
  outside the `⟨z⟩`-orbit, the abelian group `⟨g, z⟩` has an orbit of `p`-power size larger than
  `p`, hence is transitive (this is the abelian half of Marušič 1985).
* `main`: order `p²` and every graph with a transitive abelian automorphism group are done; the
  rest splits by whether the smaller prime is `2`.

Remaining hypotheses (both theorems in the literature, both restricted to graphs with no
transitive abelian group of automorphisms):
* `H1`: order `2q`, `q` an odd prime (Alspach 1979: Hamiltonian except the Petersen graph,
  which has a Hamiltonian path).
* `H2`: order `pq`, `2 < p < q` primes (Marušič 1985 / Du, Kutnar, Marušič, Combinatorica 2021).
-/

namespace OMA.R_LovaszConjecture_lovasz_conjecture_R1_H1_R1
open SimpleGraph

variable {V : Type}

lemma walk_of_chain (G : SimpleGraph V) : ∀ (L : List V) (a : V), (a :: L).IsChain G.Adj →
    ∃ b, ∃ p : G.Walk a b, p.support = a :: L
  | [], a, _ => ⟨a, Walk.nil, rfl⟩
  | (c :: L), a, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨b, p, hp⟩ := walk_of_chain G L c h.2
    exact ⟨b, Walk.cons h.1 p, by simp [hp]⟩

lemma ham_of_list [Fintype V] [DecidableEq V] (G : SimpleGraph V) (L : List V) (hne : L ≠ [])
    (hc : L.IsChain G.Adj) (hnd : L.Nodup) (hall : ∀ x, x ∈ L) :
    LovaszConjecture.HasHamiltonianPath G := by
  obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨b, p, hp⟩ := walk_of_chain G L' a hc
  refine ⟨a, b, p, fun x => ?_⟩
  rw [hp]
  exact List.count_eq_one_of_mem hnd (hall x)

lemma reach_closed (G : SimpleGraph V) (X : Set V) (hX : ∀ x y, x ∈ X → G.Adj x y → y ∈ X) :
    ∀ {u w : V} (p : G.Walk u w), u ∈ X → w ∈ X
  | _, _, Walk.nil, h => h
  | _, _, Walk.cons ha p, h => reach_closed G X hX p (hX _ _ h ha)

section Zig
variable {M : Type} [CommGroup M] [MulAction M V] (G : SimpleGraph V)

lemma good_step [Finite M] (hM : ∀ (m : M) (x y : V), G.Adj x y → G.Adj (m • x) (m • y))
    (v0 : V) (H : Subgroup M) (L : List V) (hL : (L.IsChain G.Adj ∧ L.Nodup ∧ L.head? = some v0 ∧ ∀ x, x ∈ L ↔ ∃ h ∈ H, h • v0 = x)) (s : M)
    (hs : G.Adj v0 (s • v0)) : ∃ L' : List V, (L'.IsChain G.Adj ∧ L'.Nodup ∧ L'.head? = some v0 ∧ ∀ x, x ∈ L' ↔ ∃ h ∈ (H ⊔ Subgroup.zpowers s), h • v0 = x) := by
  classical
  obtain ⟨hch, hnd, hhd, hmem⟩ := hL
  have hne : L ≠ [] := by rintro rfl; simp at hhd
  set e := L.getLast hne with he
  obtain ⟨h0, h0H, h0e⟩ := (hmem e).1 (List.getLast_mem hne)
  have hex : ∃ n, 0 < n ∧ ∃ h ∈ H, h • v0 = s ^ n • v0 :=
    ⟨orderOf s, orderOf_pos s, 1, H.one_mem, by rw [pow_orderOf_eq_one]⟩
  set m := Nat.find hex with hm
  have hm0 : 0 < m := (Nat.find_spec hex).1
  obtain ⟨h1, h1H, h1e⟩ := (Nat.find_spec hex).2
  have hmin : ∀ d, 0 < d → d < m → ∀ h ∈ H, h • v0 ≠ s ^ d • v0 := by
    intro d hd hdm h hh heq
    exact Nat.find_min hex hdm ⟨hd, h, hh, heq⟩
  -- the zigzag pieces
  let Q : ℕ → List V := fun j => (if Even j then L else L.reverse).map (fun x => s ^ j • x)
  have hQch : ∀ j, (Q j).IsChain G.Adj := by
    intro j
    simp only [Q]
    rw [List.isChain_map]
    split_ifs
    · exact hch.imp (fun a b h => hM _ _ _ h)
    · rw [List.isChain_reverse]; exact hch.imp (fun a b h => hM _ _ _ h.symm)
  have hLlast : L.getLast? = some e := List.getLast?_eq_some_getLast hne
  have hQhd : ∀ j, (Q j).head? = some (s ^ j • if Even j then v0 else e) := by
    intro j
    simp only [Q]
    split_ifs <;> simp [List.head?_map, List.head?_reverse, hhd, hLlast]
  have hQlast : ∀ j, (Q j).getLast? = some (s ^ j • if Even j then e else v0) := by
    intro j
    simp only [Q]
    split_ifs <;> simp [List.getLast?_map, List.getLast?_reverse, hhd, hLlast]
  have hQmem : ∀ j x, x ∈ Q j ↔ ∃ h ∈ H, x = s ^ j • h • v0 := by
    intro j x
    simp only [Q]
    split_ifs
    · simp only [List.mem_map, hmem]
      constructor
      · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩; exact ⟨h, hh, rfl⟩
      · rintro ⟨h, hh, rfl⟩; exact ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    · simp only [List.mem_map, List.mem_reverse, hmem]
      constructor
      · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩; exact ⟨h, hh, rfl⟩
      · rintro ⟨h, hh, rfl⟩; exact ⟨_, ⟨h, hh, rfl⟩, rfl⟩
  have hQnd : ∀ j, (Q j).Nodup := by
    intro j
    simp only [Q]
    split_ifs
    · exact hnd.map (MulAction.injective _)
    · exact (List.nodup_reverse.mpr hnd).map (MulAction.injective _)
  have hadj : ∀ (g : M) (k : ℕ), G.Adj (s ^ k • g • v0) (s ^ (k + 1) • g • v0) := by
    intro g k
    have h2 : s ^ (k + 1) • g • v0 = (s ^ k * g) • (s • v0) := by
      rw [← mul_smul, ← mul_smul, pow_succ, mul_right_comm]
    rw [h2, ← mul_smul]
    exact hM _ _ _ hs
  have hw : ∀ k : ℕ, ∃ g : M, (if Even k then e else v0) = g • v0 := by
    intro k
    split_ifs
    · exact ⟨h0, h0e.symm⟩
    · exact ⟨1, (one_smul _ _).symm⟩
  let build : ℕ → List V := fun k => (List.range (k + 1)).flatMap Q
  have hb0 : build 0 = Q 0 := by simp [build]
  have hbs : ∀ k, build (k + 1) = build k ++ Q (k + 1) := by
    intro k
    simp only [build]
    rw [List.range_succ, List.flatMap_append]
    simp
  have key : ∀ k, (build k).IsChain G.Adj ∧ (build k).head? = some v0 ∧
      (build k).getLast? = some (s ^ k • if Even k then e else v0) ∧
      (∀ x, x ∈ build k ↔ ∃ j ≤ k, ∃ h ∈ H, x = s ^ j • h • v0) ∧
      (k < m → (build k).Nodup) := by
    intro k
    induction k with
    | zero =>
      rw [hb0]
      refine ⟨hQch 0, by simpa using hQhd 0, hQlast 0, fun x => ?_, fun _ => hQnd 0⟩
      rw [hQmem]
      constructor
      · rintro ⟨h, hh, rfl⟩; exact ⟨0, le_rfl, h, hh, rfl⟩
      · rintro ⟨j, hj, h, hh, rfl⟩
        obtain rfl : j = 0 := by omega
        exact ⟨h, hh, rfl⟩
    | succ k ih =>
      obtain ⟨ich, ihd, ilast, imem, ind⟩ := ih
      rw [hbs]
      have hsame : (if Even (k + 1) then v0 else e) = (if Even k then e else v0) := by
        by_cases hk : Even k
        · have : ¬ Even (k + 1) := Nat.not_even_iff_odd.mpr hk.add_one
          simp [hk, this]
        · have : Even (k + 1) := (Nat.not_even_iff_odd.mp hk).add_one
          simp [hk, this]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [List.isChain_append]
        refine ⟨ich, hQch _, ?_⟩
        intro x hx y hy
        rw [ilast, Option.mem_def, Option.some_inj] at hx
        rw [hQhd, hsame, Option.mem_def, Option.some_inj] at hy
        subst hx; subst hy
        obtain ⟨g, hg⟩ := hw k
        rw [hg]
        exact hadj g k
      · rw [List.head?_append, ihd]; rfl
      · rw [List.getLast?_append, hQlast]; rfl
      · intro x
        rw [List.mem_append, imem, hQmem]
        constructor
        · rintro (⟨j, hj, h, hh, rfl⟩ | ⟨h, hh, rfl⟩)
          · exact ⟨j, by omega, h, hh, rfl⟩
          · exact ⟨k + 1, le_rfl, h, hh, rfl⟩
        · rintro ⟨j, hj, h, hh, rfl⟩
          rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
          · exact Or.inl ⟨j, by omega, h, hh, rfl⟩
          · obtain rfl : j = k + 1 := by omega
            exact Or.inr ⟨h, hh, rfl⟩
      · intro hkm
        rw [List.nodup_append]
        refine ⟨ind (by omega), hQnd _, ?_⟩
        intro a ha b hb hab
        obtain ⟨j, hj, h, hh, rfl⟩ := (imem a).1 ha
        obtain ⟨h', hh', rfl⟩ := (hQmem _ b).1 hb
        set d := k + 1 - j with hd
        have hsplit : s ^ (k + 1) = s ^ j * s ^ d := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit, mul_smul] at hab
        have h3 : h • v0 = s ^ d • h' • v0 := smul_left_cancel _ hab
        apply hmin d (by omega) (by omega) (h'⁻¹ * h) (H.mul_mem (H.inv_mem hh') hh)
        rw [mul_smul, h3, ← mul_smul, ← mul_smul, mul_comm h'⁻¹ (s ^ d), mul_assoc,
          inv_mul_cancel, mul_one]
  rw [← hm] at h1e
  obtain ⟨fch, fhd, -, fmem, fnd⟩ := key (m - 1)
  refine ⟨build (m - 1), fch, fnd (by omega), fhd, fun x => ?_⟩
  rw [fmem]
  have hq : ∀ q : ℕ, ∃ h ∈ H, s ^ (m * q) • v0 = h • v0 := by
    intro q
    induction q with
    | zero => exact ⟨1, H.one_mem, by simp⟩
    | succ q ih =>
      obtain ⟨hq, hqH, hqe⟩ := ih
      refine ⟨h1 * hq, H.mul_mem h1H hqH, ?_⟩
      rw [Nat.mul_succ, pow_add, mul_smul, ← h1e, ← mul_smul, mul_comm (s ^ (m * q)) h1,
        mul_smul, hqe, ← mul_smul]
  constructor
  · rintro ⟨j, hj, h, hh, rfl⟩
    refine ⟨h * s ^ j, Subgroup.mul_mem_sup hh (Subgroup.npow_mem_zpowers s j), ?_⟩
    rw [mul_comm, mul_smul]
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hg
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
    obtain ⟨hq', hq'H, hq'e⟩ := hq (n / m)
    refine ⟨n % m, by have := Nat.mod_lt n hm0; omega, y * hq', H.mul_mem hy hq'H, ?_⟩
    have hn : s ^ n = s ^ (n % m) * s ^ (m * (n / m)) := by rw [← pow_add, Nat.mod_add_div]
    rw [hn, mul_smul, mul_smul, hq'e]
    simp only [← mul_smul]
    congr 1
    exact mul_left_comm _ _ _

lemma good_list [Finite M] (hM : ∀ (m : M) (x y : V), G.Adj x y → G.Adj (m • x) (m • y))
    (v0 : V) : ∀ l : List M, (∀ s ∈ l, G.Adj v0 (s • v0)) →
    ∃ L : List V, (L.IsChain G.Adj ∧ L.Nodup ∧ L.head? = some v0 ∧ ∀ x, x ∈ L ↔ ∃ h ∈ (Subgroup.closure {x | x ∈ l}), h • v0 = x)
  | [], _ => by
    refine ⟨[v0], List.isChain_singleton _, List.nodup_singleton _, rfl, fun x => ?_⟩
    simp only [List.not_mem_nil, Set.setOf_false, Subgroup.closure_empty, Subgroup.mem_bot,
      exists_eq_left, one_smul, List.mem_singleton]
    exact eq_comm
  | (a :: l), hl => by
    obtain ⟨L, hL⟩ := good_list hM v0 l (fun s hs => hl s (List.mem_cons_of_mem a hs))
    obtain ⟨L', hL'⟩ := good_step G hM v0 _ L hL a (hl a List.mem_cons_self)
    refine ⟨L', ?_⟩
    have hset : {x | x ∈ a :: l} = {x | x ∈ l} ∪ {a} := by
      ext x; simp [or_comm]
    rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
    exact hL'

/-- **Zigzag lemma.** A connected graph on which a finite abelian group acts transitively by
automorphisms has a Hamiltonian path. -/
theorem ham_of_comm [Fintype V] [DecidableEq V] [Finite M]
    (hM : ∀ (m : M) (x y : V), G.Adj x y → G.Adj (m • x) (m • y))
    (v0 : V) (htr : ∀ x, ∃ m : M, m • v0 = x) (hc : G.Connected) :
    LovaszConjecture.HasHamiltonianPath G := by
  classical
  have : Fintype M := Fintype.ofFinite M
  set l := (Finset.univ.filter (fun s : M => G.Adj v0 (s • v0))).toList with hl
  have hl' : ∀ s ∈ l, G.Adj v0 (s • v0) := by
    intro s hs
    rw [hl, Finset.mem_toList, Finset.mem_filter] at hs
    exact hs.2
  obtain ⟨L, hch, hnd, hhd, hmem⟩ := good_list G hM v0 l hl'
  set H := Subgroup.closure {x | x ∈ l}
  have hX : ∀ x y, x ∈ {x | ∃ h ∈ H, h • v0 = x} → G.Adj x y → y ∈ {x | ∃ h ∈ H, h • v0 = x} := by
    rintro x y ⟨h, hh, rfl⟩ hxy
    obtain ⟨m', rfl⟩ := htr y
    have h2 := hM h⁻¹ _ _ hxy
    rw [inv_smul_smul, ← mul_smul] at h2
    have hmem' : h⁻¹ * m' ∈ H := by
      apply Subgroup.subset_closure
      show h⁻¹ * m' ∈ l
      rw [hl, Finset.mem_toList, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h2⟩
    refine ⟨m', ?_, rfl⟩
    have := H.mul_mem hh hmem'
    rwa [mul_inv_cancel_left] at this
  have hall : ∀ x, x ∈ L := by
    intro x
    obtain ⟨p⟩ := hc.preconnected v0 x
    exact (hmem x).2 (reach_closed G _ hX p ⟨1, H.one_mem, one_smul _ _⟩)
  have hne : L ≠ [] := by rintro rfl; simp at hhd
  exact ham_of_list G L hne hch hnd hall

end Zig

section PSq
open LovaszConjecture OMA.R_LovaszConjecture_lovasz_conjecture_R1

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V)

lemma orbit_ppow [Finite (G ≃g G)] {p : ℕ} (hp : p.Prime) (P : Subgroup (G ≃g G)) (a : ℕ)
    (hP : Nat.card P = p ^ a) (K : Subgroup (G ≃g G)) (hK : K ≤ P) (v : V) :
    ∃ j, (MulAction.orbit K v).ncard = p ^ j := by
  have h1 : (MulAction.orbit K v).ncard ∣ p ^ a := by
    rw [← MulAction.index_stabilizer, ← hP]
    exact (Subgroup.index_dvd_card _).trans (Subgroup.card_dvd_of_le hK)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h1
  exact ⟨j, hj⟩

lemma orbit_mono {K K' : Subgroup (G ≃g G)} (h : K ≤ K') (v : V) :
    MulAction.orbit K v ⊆ MulAction.orbit K' v := by
  rintro x ⟨a, rfl⟩
  exact ⟨⟨a.1, h a.2⟩, rfl⟩

lemma sylow_transitive [Finite (G ≃g G)] {p : ℕ} [hp : Fact p.Prime]
    (hcard : Fintype.card V = p ^ 2) (ht : IsVertexTransitive G) (P : Sylow p (G ≃g G))
    (v : V) : ∀ x, x ∈ MulAction.orbit (P : Subgroup (G ≃g G)) v := by
  have := isPretransitive_of_isVertexTransitive G ht
  set S := MulAction.stabilizer (G ≃g G) v with hSdef
  have hS : S.index = p ^ 2 := by
    rw [hSdef, MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, hcard]
  have h1 : (S ⊓ P).relIndex P * (P : Subgroup (G ≃g G)).index = (S ⊓ P).index :=
    Subgroup.relIndex_mul_index inf_le_right
  have h2 : S.index ∣ (S ⊓ P).index := Subgroup.index_dvd_of_le inf_le_left
  have hcop : Nat.Coprime (p ^ 2) (P : Subgroup (G ≃g G)).index :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 P.not_dvd_index)
  have h3 : p ^ 2 ∣ (S ⊓ P).relIndex P := by
    apply hcop.dvd_of_dvd_mul_right
    rw [h1, ← hS]; exact h2
  have horb : (MulAction.orbit (P : Subgroup (G ≃g G)) v).ncard = (S ⊓ P).relIndex P := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext g
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, hSdef, Subgroup.smul_def,
      RelIso.smul_def]
  have hpos : 0 < (MulAction.orbit (P : Subgroup (G ≃g G)) v).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨v, MulAction.mem_orbit_self v⟩
  have hle : p ^ 2 ≤ (MulAction.orbit (P : Subgroup (G ≃g G)) v).ncard := by
    rw [horb]; exact Nat.le_of_dvd (horb ▸ hpos) h3
  have heq : MulAction.orbit (P : Subgroup (G ≃g G)) v = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]; exact hle
  intro x
  rw [heq]; exact Set.mem_univ x

lemma exists_abelian_transitive {p : ℕ} (hp : p.Prime) (hcard : Fintype.card V = p ^ 2)
    (ht : IsVertexTransitive G) (v : V) :
    ∃ g z : G ≃g G, g * z = z * g ∧ ∀ x, x ∈ MulAction.orbit (Subgroup.closure {g, z}) v := by
  classical
  have := autFinite G
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p (G ≃g G)))
  have hPtr := sylow_transitive G hcard ht P v
  have hPtr' : ∀ x, ∃ g ∈ (P : Subgroup (G ≃g G)), g • v = x := by
    intro x
    obtain ⟨a, ha⟩ := hPtr x
    exact ⟨a.1, a.2, ha⟩
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have hcard2 : 2 ≤ Fintype.card V := by
    rw [hcard]; nlinarith [hp.two_le]
  obtain ⟨w, hw⟩ : ∃ w : V, w ≠ v := by
    by_contra hcon
    push Not at hcon
    have : Fintype.card V ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => (hcon a).trans (hcon b).symm)
    omega
  have hnt : Nontrivial (P : Subgroup (G ≃g G)) := by
    obtain ⟨g, hg, hgw⟩ := hPtr' w
    refine ⟨⟨⟨g, hg⟩, 1, fun h => ?_⟩⟩
    have : g = 1 := congrArg Subtype.val h
    subst this
    exact hw (by rw [← hgw, one_smul])
  have hcnt := IsPGroup.center_nontrivial P.isPGroup'
  obtain ⟨z', hz'⟩ := @exists_ne _ hcnt (1 : Subgroup.center (P : Subgroup (G ≃g G)))
  have hz'c := Subgroup.mem_center_iff.mp z'.2
  set z : G ≃g G := z'.1.1 with hzdef
  have hzP : z ∈ (P : Subgroup (G ≃g G)) := z'.1.2
  have hzc : ∀ h ∈ (P : Subgroup (G ≃g G)), h * z = z * h := by
    intro h hh
    have := hz'c ⟨h, hh⟩
    exact congrArg Subtype.val this
  have hz1 : z ≠ 1 := by
    intro h
    apply hz'
    apply Subtype.ext; apply Subtype.ext
    exact h
  have hzv : z • v ≠ v := by
    intro hfix
    apply hz1
    apply RelIso.ext
    intro x
    obtain ⟨h, hh, rfl⟩ := hPtr' x
    have : z • h • v = h • v := by
      rw [← mul_smul, ← hzc h hh, mul_smul, hfix]
    exact this
  -- the orbit of `zpowers z`
  set O := MulAction.orbit (Subgroup.zpowers z) v with hO
  have hzle : Subgroup.zpowers z ≤ (P : Subgroup (G ≃g G)) := Subgroup.zpowers_le.2 hzP
  obtain ⟨i, hi⟩ := orbit_ppow G hp _ a ha _ hzle v
  have hO2 : 2 ≤ O.ncard := by
    have hsub : ({v, z • v} : Set V) ⊆ O := by
      intro x hx
      rcases hx with rfl | rfl
      · exact MulAction.mem_orbit_self _
      · exact ⟨⟨z, Subgroup.mem_zpowers z⟩, rfl⟩
    have := Set.ncard_le_ncard hsub
    rwa [Set.ncard_pair (Ne.symm hzv)] at this
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, pow_zero] at hi
      change O.ncard = 1 at hi
      omega
    · exact h
  by_cases hall : ∀ x, x ∈ O
  · refine ⟨z, z, rfl, fun x => orbit_mono G ?_ v (hall x)⟩
    exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  push Not at hall
  obtain ⟨x, hx⟩ := hall
  obtain ⟨g, hg, hgx⟩ := hPtr' x
  refine ⟨g, z, hzc g hg, ?_⟩
  set A := Subgroup.closure ({g, z} : Set (G ≃g G))
  have hAP : A ≤ (P : Subgroup (G ≃g G)) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hg
    · exact hzP
  have hzA : Subgroup.zpowers z ≤ A := Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  obtain ⟨j, hj⟩ := orbit_ppow G hp _ a ha _ hAP v
  have hsub : insert x O ⊆ MulAction.orbit A v := by
    intro y hy
    rcases hy with rfl | hy
    · exact ⟨⟨g, Subgroup.subset_closure (by simp)⟩, hgx⟩
    · exact orbit_mono G hzA v hy
  have hge := Set.ncard_le_ncard hsub
  rw [Set.ncard_insert_of_notMem hx, hj, hi] at hge
  have hpi : p ≤ p ^ i := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi1
  have hj2 : 2 ≤ j := by
    by_contra hcon
    have : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one] at this
    omega
  have hle : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj2
  have heq : MulAction.orbit A v = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard, hj]; exact hle
  intro y
  rw [heq]; exact Set.mem_univ y

/-- **Order `p²`.** Every connected vertex-transitive graph of order `p²` has a Hamiltonian path. -/
theorem ham_of_card_sq {p : ℕ} (hp : p.Prime) (hcard : Fintype.card V = p ^ 2)
    (hc : G.Connected) (ht : IsVertexTransitive G) : HasHamiltonianPath G := by
  obtain ⟨v⟩ := hc.nonempty
  obtain ⟨g, z, hgz, horb⟩ := exists_abelian_transitive G hp hcard ht v
  have := autFinite G
  let _ : CommGroup (Subgroup.closure ({g, z} : Set (G ≃g G))) :=
    Subgroup.closureCommGroupOfComm (by
      intro x hx y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hgz
      · exact hgz.symm
      · rfl)
  refine ham_of_comm G (M := Subgroup.closure ({g, z} : Set (G ≃g G))) ?_ v
    (fun x => MulAction.mem_orbit_iff.mp (horb x)) hc
  intro m x y h
  exact (m.1 : G ≃g G).map_adj_iff.mpr h

end PSq


open LovaszConjecture in
/-- Order `2q`, `q` an odd prime, for graphs with no transitive abelian automorphism group. -/
def H1 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ Fintype.card V = 2 * q) →
    G.Connected → IsVertexTransitive G →
    (¬ ∃ A : Subgroup (G ≃g G), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ u w : V, ∃ a ∈ A, a u = w) →
    HasHamiltonianPath G

open LovaszConjecture in
/-- Order `pq`, `2 < p < q` primes, for graphs with no transitive abelian automorphism group. -/
def H2 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 < p ∧ p < q ∧ Fintype.card V = p * q) →
    G.Connected → IsVertexTransitive G →
    (¬ ∃ A : Subgroup (G ≃g G), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ u w : V, ∃ a ∈ A, a u = w) →
    HasHamiltonianPath G

/-- A connected graph with a transitive abelian group of automorphisms has a Hamiltonian path. -/
theorem ham_of_abelian_sub {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A : Subgroup (G ≃g G)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htr : ∀ u w : V, ∃ a ∈ A, a u = w) (hc : G.Connected) :
    LovaszConjecture.HasHamiltonianPath G := by
  obtain ⟨v⟩ := hc.nonempty
  have := OMA.R_LovaszConjecture_lovasz_conjecture_R1.autFinite G
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  refine ham_of_comm G (M := A) ?_ v (fun x => ?_) hc
  · intro m x y h
    exact (m.1 : G ≃g G).map_adj_iff.mpr h
  · obtain ⟨a, ha, hax⟩ := htr v x
    exact ⟨⟨a, ha⟩, hax⟩

theorem main : H1 → H2 → OMA.R_LovaszConjecture_lovasz_conjecture_R1.H1 := by
  intro h1 h2 V _ _ G _ hcard hc ht
  obtain ⟨p, q, hp, hq, hpq⟩ := hcard
  by_cases hab : ∃ A : Subgroup (G ≃g G), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∀ u w : V, ∃ a ∈ A, a u = w
  · obtain ⟨A, hA, htr⟩ := hab
    exact ham_of_abelian_sub G A hA htr hc
  rcases lt_trichotomy p q with hlt | rfl | hgt
  · by_cases hp2 : p = 2
    · subst hp2
      exact h1 G ⟨q, hq, by omega, hpq⟩ hc ht hab
    · exact h2 G ⟨p, q, hp, hq, lt_of_le_of_ne hp.two_le (Ne.symm hp2), hlt, hpq⟩ hc ht hab
  · exact ham_of_card_sq G hp (by rw [hpq, sq]) hc ht
  · by_cases hq2 : q = 2
    · subst hq2
      exact h1 G ⟨p, hp, by omega, by rw [hpq, mul_comm]⟩ hc ht hab
    · exact h2 G ⟨q, p, hq, hp, lt_of_le_of_ne hq.two_le (Ne.symm hq2), hgt,
        by rw [hpq, mul_comm]⟩ hc ht hab

end OMA.R_LovaszConjecture_lovasz_conjecture_R1_H1_R1
