import FormalConjectures.Wikipedia.LovaszConjecture
import Mathlib

/-! Lovász's conjecture, split by the number of prime factors of the order, with the prime
order case proved inside: Turner (1967), every connected vertex-transitive graph of prime order
`p` has a Hamiltonian path. Proof of the prime case: orbit-stabilizer gives `p ∣ |Aut G|`, so by
Cauchy there is an automorphism `σ` of order `p`; its powers move a vertex `v` around all `p`
vertices; a neighbour of `v` is `σ ^ s v`, and `τ = σ ^ s` (still of order `p`) gives the
Hamiltonian path `v, τ v, ..., τ ^ (p - 1) v`. Orders `0` and `1` are trivial. The remaining
orders are products of exactly two primes (H1; includes the known cases `2p` (Alspach) and `p²`
(Marušič), `pq` open in general) and orders with at least three prime factors counted with
multiplicity (H2). -/

namespace OMA.R_LovaszConjecture_lovasz_conjecture_R1
open SimpleGraph LovaszConjecture

/-- Lovász's conjecture for graphs whose order is a product of two primes. -/
def H1 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Fintype.card V = p * q) →
    G.Connected → LovaszConjecture.IsVertexTransitive G → LovaszConjecture.HasHamiltonianPath G

/-- Lovász's conjecture for graphs whose order has at least three prime factors (with
multiplicity). -/
def H2 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∃ p q r m : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ 0 < m ∧ Fintype.card V = p * q * r * m) →
    G.Connected → LovaszConjecture.IsVertexTransitive G → LovaszConjecture.HasHamiltonianPath G

section Turner

variable {V : Type}

/-- A walk `f 0, f 1, ..., f n` along consecutive adjacencies, with its support. -/
lemma exists_fwalk (G : SimpleGraph V) (f : ℕ → V) (hf : ∀ i, G.Adj (f i) (f (i + 1))) :
    ∀ n : ℕ, ∃ p : G.Walk (f 0) (f n), p.support = (List.range (n + 1)).map f
  | 0 => ⟨Walk.nil, by simp⟩
  | n + 1 => by
    obtain ⟨p, hp⟩ := exists_fwalk G f hf n
    refine ⟨p.concat (hf n), ?_⟩
    rw [Walk.support_concat, hp,
      show List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] from List.range_succ,
      List.map_append]
    simp

lemma fwalk_isHamiltonian [Fintype V] [DecidableEq V] (G : SimpleGraph V) (f : ℕ → V)
    (n : ℕ) (hn : n + 1 = Fintype.card V) {p : G.Walk (f 0) (f n)}
    (hp : p.support = (List.range (n + 1)).map f)
    (hinj : Set.InjOn f (Set.Iio (n + 1))) : p.IsHamiltonian := by
  have hnd : ((List.range (n + 1)).map f).Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy h
    exact hinj (by simpa using hx) (by simpa using hy) h
  have hcard : ((List.range (n + 1)).map f).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hnd]
    simp [hn]
  intro a
  rw [hp]
  apply List.count_eq_one_of_mem hnd
  have : a ∈ ((List.range (n + 1)).map f).toFinset := by rw [hcard]; exact Finset.mem_univ a
  exact List.mem_toFinset.mp this

/-- If `g` has prime order and moves `v`, then `i ↦ g ^ i • v` is injective below `orderOf g`. -/
lemma pow_smul_injOn {M : Type*} [Group M] [MulAction M V] (g : M) (hp : (orderOf g).Prime)
    (v : V) (hv : g • v ≠ v) :
    Set.InjOn (fun i : ℕ => g ^ i • v) (Set.Iio (orderOf g)) := by
  have key : ∀ k, 0 < k → k < orderOf g → g ^ k • v = v → False := by
    intro k hk0 hkp hk
    have hfix : ∀ m : ℕ, (g ^ k) ^ m • v = v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, mul_smul, hk, ih]
    have hcop : Nat.Coprime k (orderOf g) :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hk0 hkp))
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hgm : (g ^ k) ^ m = g := by
      rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
    exact hv (hgm ▸ hfix m)
  have shift : ∀ i j, i < j → j < orderOf g → g ^ i • v = g ^ j • v → False := by
    intro i j hij hj h
    apply key (j - i) (by omega) (by omega)
    have h2 : g ^ i • (g ^ (j - i) • v) = g ^ i • v := by
      rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hij.le, h]
    exact smul_left_cancel _ h2
  intro i hi j hj hij
  simp only [Set.mem_Iio] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact shift i j h hj hij
  · exact shift j i h hi hij.symm

/-- The automorphism group of a finite graph is finite. -/
lemma autFinite [Finite V] (G : SimpleGraph V) : Finite (G ≃g G) :=
  Finite.of_injective (fun φ : G ≃g G => (φ : V ≃ V)) (fun _ _ h =>
    RelIso.ext (fun x => congrArg (fun e : V ≃ V => e x) h))

/-- Vertex-transitivity as `IsPretransitive` of the automorphism group. -/
lemma isPretransitive_of_isVertexTransitive (G : SimpleGraph V) (ht : IsVertexTransitive G) :
    MulAction.IsPretransitive (G ≃g G) V :=
  ⟨fun u v => by obtain ⟨φ, hφ⟩ := ht u v; exact ⟨φ, hφ⟩⟩

/-- `card V` divides the order of the automorphism group of a vertex-transitive graph. -/
lemma card_dvd_card_aut [Finite V] [Nonempty V] (G : SimpleGraph V) (ht : IsVertexTransitive G) :
    Nat.card V ∣ Nat.card (G ≃g G) := by
  have := isPretransitive_of_isVertexTransitive G ht
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  rw [← MulAction.index_stabilizer_of_transitive (G ≃g G) v]
  exact Subgroup.index_dvd_card _

/-- Cauchy: a vertex-transitive graph of prime order has an automorphism of order `card V`. -/
lemma exists_aut_orderOf [Fintype V] (G : SimpleGraph V) (hp : (Fintype.card V).Prime)
    (ht : IsVertexTransitive G) : ∃ σ : G ≃g G, orderOf σ = Fintype.card V := by
  have := autFinite G
  have : Fact (Fintype.card V).Prime := ⟨hp⟩
  have : Nonempty V := Fintype.card_pos_iff.mp hp.pos
  have h := card_dvd_card_aut G ht
  rw [Nat.card_eq_fintype_card] at h
  exact exists_prime_orderOf_dvd_card' _ h

/-- In a connected graph with at least two vertices every vertex has a neighbour. -/
lemma exists_adj_of_connected [Fintype V] (G : SimpleGraph V) (hc : G.Connected)
    (h2 : 2 ≤ Fintype.card V) (v : V) : ∃ w, G.Adj v w := by
  obtain ⟨w, hw⟩ : ∃ w, w ≠ v := by
    by_contra hcon
    push Not at hcon
    have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (hcon a).trans (hcon b).symm)
    omega
  obtain ⟨p⟩ := hc.preconnected v w
  cases p with
  | nil => exact absurd rfl hw
  | cons h _ => exact ⟨_, h⟩

/-- An element of order `≠ 1` acting faithfully moves some point. -/
lemma exists_smul_ne (G : SimpleGraph V) (σ : G ≃g G) (hσ : σ ≠ 1) : ∃ v : V, σ • v ≠ v := by
  by_contra h
  push Not at h
  exact hσ (RelIso.ext (fun x => h x))

/-- Surjectivity from injectivity on `Iio (card V)`. -/
lemma exists_eq_of_injOn [Fintype V] [DecidableEq V] (f : ℕ → V) (hinj : Set.InjOn f (Set.Iio (Fintype.card V)))
    (w : V) : ∃ i < Fintype.card V, f i = w := by
  have himg : (Finset.range (Fintype.card V)).image f = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hio : Set.InjOn f (Finset.range (Fintype.card V) : Set ℕ) := by
      intro x hx y hy h
      exact hinj (by simpa using hx) (by simpa using hy) h
    rw [Finset.card_image_of_injOn hio]
    simp
  have : w ∈ (Finset.range (Fintype.card V)).image f := by rw [himg]; exact Finset.mem_univ w
  simpa using this

/-- **Turner (1967)**: a connected vertex-transitive graph of prime order has a Hamiltonian
path. -/
theorem turner [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : (Fintype.card V).Prime) (hc : G.Connected) (ht : IsVertexTransitive G) :
    HasHamiltonianPath G := by
  obtain ⟨σ, hσ⟩ := exists_aut_orderOf G hp ht
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  obtain ⟨v, hv⟩ := exists_smul_ne G σ hσ1
  have hinjσ := pow_smul_injOn σ (hσ ▸ hp) v hv
  rw [hσ] at hinjσ
  obtain ⟨w, hvw⟩ := exists_adj_of_connected G hc hp.two_le v
  obtain ⟨s, hs, hsw⟩ := exists_eq_of_injOn (fun i : ℕ => σ ^ i • v) hinjσ w
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_smul] at hsw
    exact G.ne_of_adj hvw hsw
  set τ := σ ^ s with hτdef
  have hτ : orderOf τ = Fintype.card V := by
    rw [hτdef, Nat.Coprime.orderOf_pow, hσ]
    rw [hσ]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hs0) hs)
  have hτv : τ • v = w := hsw
  have hτne : τ • v ≠ v := by
    rw [hτv]; exact (G.ne_of_adj hvw).symm
  have hinjτ := pow_smul_injOn τ (hτ ▸ hp) v hτne
  rw [hτ] at hinjτ
  have hadj : ∀ i : ℕ, G.Adj (τ ^ i • v) (τ ^ (i + 1) • v) := by
    intro i
    have h1 : τ ^ (i + 1) • v = τ ^ i • (τ • v) := by rw [pow_succ, mul_smul]
    rw [h1, hτv]
    simp only [RelIso.smul_def]
    exact (τ ^ i).map_adj_iff.mpr hvw
  have hn1 : Fintype.card V - 1 + 1 = Fintype.card V := by have := hp.two_le; omega
  obtain ⟨W, hW⟩ := exists_fwalk G (fun i : ℕ => τ ^ i • v) hadj (Fintype.card V - 1)
  refine ⟨_, _, W, ?_⟩
  apply fwalk_isHamiltonian G (fun i : ℕ => τ ^ i • v) (Fintype.card V - 1) hn1 hW
  rw [hn1]
  exact hinjτ

end Turner

/-- Every natural number `n ≥ 2` that is not prime is a product of two primes or has at least
three prime factors. -/
lemma composite_cases (n : ℕ) (h2 : 2 ≤ n) (hnp : ¬ n.Prime) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) ∨
    (∃ p q r m : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ 0 < m ∧ n = p * q * r * m) := by
  have hn1 : n ≠ 1 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  obtain ⟨k, hk⟩ := Nat.minFac_dvd n
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · omega
      · rw [mul_one] at hk; exact absurd (hk ▸ hp) hnp
    · exact h
  by_cases hkp : k.Prime
  · exact Or.inl ⟨n.minFac, k, hp, hkp, hk⟩
  · right
    have hk1 : k ≠ 1 := by omega
    have hq : k.minFac.Prime := Nat.minFac_prime hk1
    obtain ⟨j, hj⟩ := Nat.minFac_dvd k
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · interval_cases j
        · omega
        · rw [mul_one] at hj; exact absurd (hj ▸ hq) hkp
      · exact h
    have hj1 : j ≠ 1 := by omega
    obtain ⟨m, hm⟩ := Nat.minFac_dvd j
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm; omega
      · exact h
    refine ⟨n.minFac, k.minFac, j.minFac, m, hp, hq, Nat.minFac_prime hj1, hm0, ?_⟩
    rw [mul_assoc, mul_assoc, ← hm, ← hj]
    exact hk

theorem main : H1 → H2 → type_of% @LovaszConjecture.lovasz_conjecture := by
  intro h1 h2 V _ _ G _ hc ht
  have hne : Nonempty V := hc.nonempty
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  by_cases hone : Fintype.card V = 1
  · have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hone.le
    obtain ⟨v⟩ := hne
    exact ⟨v, v, Walk.nil, Walk.IsHamiltonian.of_subsingleton⟩
  by_cases hp : (Fintype.card V).Prime
  · exact turner G hp hc ht
  rcases composite_cases (Fintype.card V) (by omega) hp with h | h
  · exact h1 G h hc ht
  · exact h2 G h hc ht

end OMA.R_LovaszConjecture_lovasz_conjecture_R1
