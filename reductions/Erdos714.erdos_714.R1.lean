import FormalConjectures.ErdosProblems.«714»

/-!
# Erdős 714: the case r = 2 (Klein; Erdős–Rényi–Sós and Brown 1966)

Proved inside (`case_two`): ex(n; K_{2,2}) ≥ n^{3/2} / 64 for all n ≥ 16.
Construction (`graph_bound`): for a prime p, the affine point-line incidence graph over ZMod p
(point (x, y) adjacent to line (m, c) iff y = m x + c) has p^3 edges and no K_{2,2}, since two
distinct points lie on at most one common line; padding with isolated vertices gives
p^3 ≤ ex(2 p^2 + k; K_{2,2}). Bertrand's postulate picks p with √n < 4p and 2p^2 ≤ n.
H1 is the case r = 3 (Brown 1966, known, via unit spheres over F_p^3).
H2 is every r ≥ 4 (open; known only for K_{r,s} with s > (r-1)!, Kollár–Rónyai–Szabó, Alon–Rónyai–Szabó).
-/

namespace OMA.R_Erdos714_erdos_714_R1

open Filter SimpleGraph

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ) ^ ((2 : ℝ) - 1 / (3 : ℝ)) ≤
      (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ)

def H2 : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
      (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)

/-- Two distinct points of the affine plane lie on at most one common non-vertical line. -/
lemma incidence_key {F : Type*} [Field F] (x1 y1 x2 y2 m1 c1 m2 c2 : F)
    (hP : (x1, y1) ≠ (x2, y2)) (hL : (m1, c1) ≠ (m2, c2))
    (h11 : y1 = m1 * x1 + c1) (h12 : y1 = m2 * x1 + c2)
    (h21 : y2 = m1 * x2 + c1) (h22 : y2 = m2 * x2 + c2) : False := by
  have h : (m1 - m2) * (x1 - x2) = 0 := by linear_combination -h11 + h12 + h21 - h22
  rcases mul_eq_zero.1 h with h | h
  · have hm : m1 = m2 := sub_eq_zero.1 h
    subst hm
    exact hL (by rw [show c1 = c2 by linear_combination h12 - h11])
  · have hx : x1 = x2 := sub_eq_zero.1 h
    subst hx
    exact hP (by rw [show y1 = y2 by linear_combination h11 - h21])

/-- The affine point-line incidence graph over `ZMod p`, padded with `k` isolated vertices,
is `K_{2,2}`-free with `p^3` edges. -/
theorem graph_bound (p : ℕ) (hp : p.Prime) (k : ℕ) :
    p ^ 3 ≤ extremalNumber (2 * p ^ 2 + k) (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let r : ((ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)) ⊕ Fin k →
      ((ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)) ⊕ Fin k → Prop :=
    fun u v => ∃ x y m c : ZMod p, u = Sum.inl (Sum.inl (x, y)) ∧
      v = Sum.inl (Sum.inr (m, c)) ∧ y = m * x + c
  let G := SimpleGraph.fromRel r
  have hcard : Fintype.card (((ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)) ⊕ Fin k) = 2 * p ^ 2 + k := by
    simp [ZMod.card]; ring
  -- adjacency facts
  have adjP : ∀ (x y : ZMod p) z, G.Adj (Sum.inl (Sum.inl (x, y))) z →
      ∃ m c : ZMod p, z = Sum.inl (Sum.inr (m, c)) ∧ y = m * x + c := by
    intro x y z h
    simp only [G, r, fromRel_adj] at h
    obtain ⟨-, ⟨x', y', m, c, h1, rfl, h3⟩ | ⟨x', y', m, c, h1, h2, h3⟩⟩ := h
    · simp only [Sum.inl.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨m, c, rfl, h3⟩
    · simp at h2
  have adjL : ∀ (m c : ZMod p) z, G.Adj (Sum.inl (Sum.inr (m, c))) z →
      ∃ x y : ZMod p, z = Sum.inl (Sum.inl (x, y)) ∧ y = m * x + c := by
    intro m c z h
    simp only [G, r, fromRel_adj] at h
    obtain ⟨-, ⟨x', y', m', c', h1, h2, h3⟩ | ⟨x', y', m', c', rfl, h2, h3⟩⟩ := h
    · simp at h1
    · simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨x', y', rfl, h3⟩
  have adjI : ∀ (i : Fin k) z, ¬ G.Adj (Sum.inr i) z := by
    intro i z h
    simp only [G, r, fromRel_adj] at h
    obtain ⟨-, ⟨x', y', m', c', h1, h2, h3⟩ | ⟨x', y', m', c', h1, h2, h3⟩⟩ := h
    · simp at h1
    · simp at h2
  have key : ∀ u v w z, u ≠ v → w ≠ z → G.Adj u w → G.Adj u z → G.Adj v w →
      G.Adj v z → False := by
    intro u v w z huv hwz huw huz hvw hvz
    rcases u with ((⟨x1, y1⟩ | ⟨m1, c1⟩) | i)
    · obtain ⟨m1, c1, rfl, h11⟩ := adjP _ _ _ huw
      obtain ⟨m2, c2, rfl, h12⟩ := adjP _ _ _ huz
      obtain ⟨x2, y2, rfl, h21⟩ := adjL _ _ _ hvw.symm
      obtain ⟨m2', c2', e, h22⟩ := adjP _ _ _ hvz
      simp only [Sum.inl.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact incidence_key x1 y1 x2 y2 m1 c1 m2 c2 (fun h => huv (by rw [h]))
        (fun h => hwz (by rw [h])) h11 h12 h21 h22
    · obtain ⟨x1, y1, rfl, h11⟩ := adjL _ _ _ huw
      obtain ⟨x2, y2, rfl, h21⟩ := adjL _ _ _ huz
      obtain ⟨m2, c2, rfl, h12⟩ := adjP _ _ _ hvw.symm
      obtain ⟨x2', y2', e, h22⟩ := adjL _ _ _ hvz
      simp only [Sum.inl.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact incidence_key x1 y1 x2 y2 m1 c1 m2 c2 (fun h => hwz (by rw [h]))
        (fun h => huv (by rw [h])) h11 h12 h21 h22
    · exact adjI i w huw
  have hfree : (completeBipartiteGraph (Fin 2) (Fin 2)).Free G := by
    rintro ⟨f⟩
    have hadj : ∀ i j : Fin 2, G.Adj (f (Sum.inl i)) (f (Sum.inr j)) := fun i j =>
      f.toHom.map_adj (by simp [completeBipartiteGraph])
    have hinj := f.injective
    exact key (f (Sum.inl 0)) (f (Sum.inl 1)) (f (Sum.inr 0)) (f (Sum.inr 1))
      (fun h => absurd (hinj h) (by simp)) (fun h => absurd (hinj h) (by simp))
      (hadj 0 0) (hadj 0 1) (hadj 1 0) (hadj 1 1)
  have hedge : p ^ 3 ≤ G.edgeFinset.card := by
    let φ : ZMod p × ZMod p × ZMod p → Sym2 (((ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)) ⊕ Fin k) :=
      fun t => s(Sum.inl (Sum.inl (t.1, t.2.1 * t.1 + t.2.2)), Sum.inl (Sum.inr (t.2.1, t.2.2)))
    have h1 : (Finset.univ : Finset (ZMod p × ZMod p × ZMod p)).card = p ^ 3 := by
      simp [ZMod.card]; ring
    rw [← h1]
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro t _
      simp only [Finset.mem_coe, mem_edgeFinset, φ, mem_edgeSet, G, r, fromRel_adj]
      refine ⟨by simp, Or.inl ⟨t.1, _, t.2.1, t.2.2, rfl, rfl, rfl⟩⟩
    · rintro ⟨x, m, c⟩ _ ⟨x', m', c'⟩ _ h
      simp only [φ, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
        reduceCtorEq, and_false, or_false] at h
      obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := h
      rfl
  calc p ^ 3 ≤ G.edgeFinset.card := hedge
    _ ≤ extremalNumber (Fintype.card (((ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)) ⊕ Fin k))
          (completeBipartiteGraph (Fin 2) (Fin 2)) := card_edgeFinset_le_extremalNumber hfree
    _ = _ := by rw [hcard]

/-- The `r = 2` case: `ex(n; K_{2,2}) ≥ n^{3/2} / 64` for `n ≥ 16`. -/
theorem case_two : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ) ^ ((2 : ℝ) - 1 / ((2 : ℕ) : ℝ)) ≤
      (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) := by
  refine ⟨1 / 64, by norm_num, eventually_atTop.2 ⟨16, fun n hn => ?_⟩⟩
  set s := Nat.sqrt n with hs
  have hs4 : 4 ≤ s := Nat.le_sqrt.2 (by omega)
  obtain ⟨p, hp, hqp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (s / 4) (by omega)
  have hss : s * s ≤ n := Nat.sqrt_le n
  have hpn : 2 * p ^ 2 ≤ n := by
    have h4 : 4 * (s / 4) ≤ s := Nat.mul_div_le s 4
    have hpp : p * p ≤ (2 * (s / 4)) * (2 * (s / 4)) := Nat.mul_le_mul hp2 hp2
    have : (4 * (s / 4)) * (4 * (s / 4)) ≤ s * s := Nat.mul_le_mul h4 h4
    nlinarith
  have hsp : s + 1 ≤ 4 * p := by omega
  have hex := graph_bound p hp (n - 2 * p ^ 2)
  rw [show 2 * p ^ 2 + (n - 2 * p ^ 2) = n by omega] at hex
  have hexR : ((p : ℝ)) ^ 3 ≤ (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) := by
    exact_mod_cast hex
  have e : (n : ℝ) ^ ((2 : ℝ) - 1 / ((2 : ℕ) : ℝ)) = (Real.sqrt n) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  rw [e]
  have hsq : Real.sqrt n < 4 * p := by
    rw [Real.sqrt_lt' (by have := hp.pos; positivity)]
    have h1 : n < (s + 1) ^ 2 := Nat.lt_succ_sqrt' n
    have h2 : (s + 1) ^ 2 ≤ (4 * p) ^ 2 := Nat.pow_le_pow_left hsp 2
    exact_mod_cast h1.trans_le h2
  have h0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h3 : (Real.sqrt n / 4) ^ 3 ≤ (p : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  calc 1 / 64 * Real.sqrt n ^ 3 = (Real.sqrt n / 4) ^ 3 := by ring
    _ ≤ _ := h3.trans hexR

theorem main : H1 → H2 → type_of% @Erdos714.erdos_714 := by
  intro h1 h2 r hr
  rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | h
  · exact case_two
  · obtain ⟨c, hc, hev⟩ := h1
    exact ⟨c, hc, by simpa using hev⟩
  · exact h2 r h

end OMA.R_Erdos714_erdos_714_R1
