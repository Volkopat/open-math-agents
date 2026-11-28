import OMAStatements.S_mo_487213
import Mathlib

/-!
# A double-ended-fork antichain of finite interval orders

Richard Stanley asks whether finite interval orders are well-quasi-ordered
under induced containment (MathOverflow 487213). We use the classical
double-ended-fork graph antichain, described for instance by Brignall and
Vatter, and represent the forks by explicit closed intervals.
Lozin and Mayhill (2011) obtained a stronger result for unit interval graphs,
using a different family.
-/

namespace Fork

abbrev Vertex (n : ℕ) := Fin (n + 2) ⊕ (Bool × Bool)

/-- Two branching spine endpoints joined by a path of length n+1, with two leaves at each end. -/
def adj (n : ℕ) : Vertex n → Vertex n → Prop
  | .inl i, .inl j => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | .inl i, .inr t | .inr t, .inl i => if t.1 then i.val = n+1 else i.val = 0
  | .inr _, .inr _ => False

end Fork

namespace Fork

private def leftEnd (n : ℕ) : Vertex n := .inl ⟨0, by omega⟩
private def rightEnd (n : ℕ) : Vertex n := .inl ⟨n+1, by omega⟩

private def branches (n : ℕ) (x : Vertex n) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ adj n x a ∧ adj n x b ∧ adj n x c

private lemma branches_left (n : ℕ) : branches n (leftEnd n) := by
  refine ⟨.inr (false,false), .inr (false,true), .inl ⟨1, by omega⟩, ?_⟩
  simp [leftEnd, adj]

private lemma branches_right (n : ℕ) : branches n (rightEnd n) := by
  refine ⟨.inr (true,false), .inr (true,true), .inl ⟨n, by omega⟩, ?_⟩
  simp [rightEnd, adj]

private lemma leaf_unique {n : ℕ} (s t : Bool) {x y : Vertex n}
    (hx : adj n (.inr (s,t)) x) (hy : adj n (.inr (s,t)) y) : x = y := by
  cases x with
  | inr => exact hx.elim
  | inl i =>
    cases y with
    | inr => exact hy.elim
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      cases s <;> simp_all [adj]

private lemma interior_neighbor {n : ℕ} {i : Fin (n+2)}
    (h0 : i.val ≠ 0) (he : i.val ≠ n+1) {y : Vertex n} (h : adj n (.inl i) y) :
    ∃ j : Fin (n+2), y = .inl j ∧ (i.val+1=j.val ∨ j.val+1=i.val) := by
  cases y with
  | inl j => exact ⟨j, rfl, h⟩
  | inr t =>
    obtain ⟨s,b⟩ := t
    cases s <;> simp_all [adj]

private lemma branches_are_ends {n : ℕ} {x : Vertex n} (h : branches n x) :
    x = leftEnd n ∨ x = rightEnd n := by
  obtain ⟨a,b,c,hab,hac,hbc,ha,hb,hc⟩ := h
  cases x with
  | inr t => exact (hab (leaf_unique t.1 t.2 ha hb)).elim
  | inl i =>
    by_cases h0 : i.val = 0
    · exact Or.inl (congrArg Sum.inl (Fin.ext h0))
    by_cases he : i.val = n+1
    · exact Or.inr (congrArg Sum.inl (Fin.ext he))
    obtain ⟨ia,rfl,hai⟩ := interior_neighbor h0 he ha
    obtain ⟨ib,rfl,hbi⟩ := interior_neighbor h0 he hb
    obtain ⟨ic,rfl,hci⟩ := interior_neighbor h0 he hc
    have h1 : ia.val ≠ ib.val := fun h => hab (congrArg Sum.inl (Fin.ext h))
    have h2 : ia.val ≠ ic.val := fun h => hac (congrArg Sum.inl (Fin.ext h))
    have h3 : ib.val ≠ ic.val := fun h => hbc (congrArg Sum.inl (Fin.ext h))
    omega

private lemma branches_map {n m : ℕ} {f : Vertex n → Vertex m} (hf : Function.Injective f)
    (h : ∀ x y, adj n x y → adj m (f x) (f y)) {x : Vertex n} (hx : branches n x) :
    branches m (f x) := by
  obtain ⟨a,b,c,h1,h2,h3,ha,hb,hc⟩ := hx
  exact ⟨f a, f b, f c, fun hh => h1 (hf hh), fun hh => h2 (hf hh), fun hh => h3 (hf hh),
    h _ _ ha, h _ _ hb, h _ _ hc⟩

/-- Collapse the two leaves at each end to the endpoint coordinate. -/
private def coord (n : ℕ) : Vertex n → ℕ
  | .inl i => i.val
  | .inr t => if t.1 then n+1 else 0

private lemma step_dist {n : ℕ} {x y : Vertex n} (h : adj n x y) :
    Nat.dist (coord n x) (coord n y) ≤ 1 := by
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      change i.val+1=j.val ∨ j.val+1=i.val at h
      change Nat.dist i.val j.val ≤ 1
      unfold Nat.dist
      omega
    | inr t =>
      obtain ⟨s,b⟩ := t
      cases s <;> simp_all [adj, coord, Nat.dist]
  | inr t =>
    cases y with
    | inl i =>
      obtain ⟨s,b⟩ := t
      cases s <;> simp_all [adj, coord, Nat.dist]
    | inr => exact h.elim

private lemma path_dist {n m : ℕ} (f : Vertex n → Vertex m)
    (h : ∀ x y, adj n x y → adj m (f x) (f y)) :
    Nat.dist (coord m (f (leftEnd n))) (coord m (f (rightEnd n))) ≤ n+1 := by
  have bound (k : ℕ) (hk : k < n+2) : Nat.dist (coord m (f (leftEnd n)))
      (coord m (f (.inl ⟨k,hk⟩))) ≤ k := by
    induction k with
    | zero => exact (Nat.dist_self _).le
    | succ k ih =>
      have hk' : k < n+2 := by omega
      let x : Vertex n := .inl ⟨k,hk'⟩
      let y : Vertex n := .inl ⟨k+1,hk⟩
      have hxy : adj n x y := Or.inl rfl
      have ht := Nat.dist.triangle_inequality (coord m (f (leftEnd n))) (coord m (f x)) (coord m (f y))
      exact ht.trans (Nat.add_le_add (ih hk') (step_dist (h x y hxy)))
  exact bound (n+1) (by omega)

/-- Injective graph homomorphisms between double-ended forks preserve the length of their spine. -/
theorem parameter_eq {n m : ℕ} (f : Vertex n → Vertex m) (hf : Function.Injective f)
    (h : ∀ x y, adj n x y → adj m (f x) (f y)) : n = m := by
  have hcard := Fintype.card_le_of_injective f hf
  simp [Vertex] at hcard
  have hsep : f (leftEnd n) ≠ f (rightEnd n) := by
    intro he
    have h' := hf he
    simp [leftEnd, rightEnd, Fin.ext_iff] at h'
  have hL := branches_are_ends (branches_map hf h (branches_left n))
  have hR := branches_are_ends (branches_map hf h (branches_right n))
  have hd := path_dist f h
  rcases hL with hL | hL <;> rcases hR with hR | hR <;>
    rw [hL, hR] at hd hsep <;> simp_all [leftEnd, rightEnd, coord, Nat.dist] <;> omega

end Fork

namespace ForkModel

open OMA.S_mo_487213

abbrev V := Fork.Vertex

private def endpoints (n : ℕ) : V n → ℕ × ℕ
  | .inl i => (12*i.val, 12*i.val+12)
  | .inr (side,leaf) =>
    let center := if side then n+1 else 0
    let start := 12*center + if leaf then 3 else 1
    (start,start+1)

private theorem inj_endpoints (n : ℕ) : Function.Injective (endpoints n) := by
  rintro (i | ⟨s,b⟩) (j | ⟨t,c⟩) h
  · simp only [endpoints, Prod.mk.injEq, Sum.inl.injEq] at h ⊢
    exact Fin.ext (by omega)
  · cases t <;> cases c <;> simp [endpoints] at h <;> omega
  · cases s <;> cases b <;> simp [endpoints] at h <;> omega
  · cases s <;> cases b <;> cases t <;> cases c <;> simp_all [endpoints] <;> omega

/-- The spine uses intervals of length twelve. The leaves at each end are
two disjoint intervals of length one inside their respective spine interval. -/
noncomputable def order (n : ℕ) : FiniteIntervalOrder where
  Vertex := V n
  finite := inferInstance
  left x := ((endpoints n x).1 : ℝ)
  right x := ((endpoints n x).2 : ℝ)
  valid := by
    rintro (i | ⟨s,b⟩)
    · simp [endpoints]
    · simp [endpoints]
  distinct := by
    intro i j h
    apply inj_endpoints n
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Prod.ext h.1 h.2

/-- Edges in the incomparability graph of a finite interval order. -/
def overlaps (P : FiniteIntervalOrder) (i j : P.Vertex) : Prop :=
  i ≠ j ∧ ¬ P.right i < P.left j ∧ ¬ P.right j < P.left i

theorem overlaps_map {P Q : FiniteIntervalOrder} (f : P.Vertex ↪ Q.Vertex)
    (hf : ∀ x y, P.right x < P.left y ↔ Q.right (f x) < Q.left (f y))
    {x y : P.Vertex} : overlaps P x y ↔ overlaps Q (f x) (f y) := by
  simp only [overlaps, f.injective.ne_iff, ← hf]

theorem overlaps_iff (n : ℕ) (i j : V n) :
    overlaps (order n) i j ↔ Fork.adj n i j := by
  change (i ≠ j ∧ ¬ ((endpoints n i).2 : ℝ) < (endpoints n j).1 ∧
    ¬ ((endpoints n j).2 : ℝ) < (endpoints n i).1) ↔ _
  simp only [Nat.cast_lt]
  rcases i with i | ⟨s,b⟩ <;> rcases j with j | ⟨t,c⟩
  · change (Sum.inl i ≠ (Sum.inl j : V n) ∧ _ ∧ _) ↔ _
    simp only [endpoints, Fork.adj, ne_eq, Sum.inl.injEq, ← Fin.val_inj]
    omega
  · change ((Sum.inl i : V n) ≠ Sum.inr (t,c) ∧ _ ∧ _) ↔ _
    rw [and_iff_right (by simp)]
    cases t <;> cases c <;> simp only [Fork.adj, endpoints, reduceIte, Bool.false_eq_true,
      Nat.mul_zero, zero_add] <;> omega
  · change ((Sum.inr (s,b) : V n) ≠ Sum.inl j ∧ _ ∧ _) ↔ _
    rw [and_iff_right (by simp)]
    cases s <;> cases b <;> simp only [Fork.adj, endpoints, reduceIte, Bool.false_eq_true,
      Nat.mul_zero, zero_add] <;> omega
  · cases s <;> cases b <;> cases t <;> cases c <;> simp [Fork.adj,endpoints] <;> omega

end ForkModel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_487213.main) := by
  intro h
  obtain ⟨i, j, hij, f, hf⟩ := h ForkModel.order
  have same : i = j := Fork.parameter_eq f f.injective fun x y hxy =>
    (ForkModel.overlaps_iff j (f x) (f y)).mp <|
      (ForkModel.overlaps_map f hf).mp <| (ForkModel.overlaps_iff i x y).mpr hxy
  omega
