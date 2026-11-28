import FormalConjectures.Wikipedia.LinearArboricityConjecture

/-!
# Reduction of the linear arboricity conjecture to regular graphs

Akiyama, Exoo and Harary (1981): it suffices to treat regular graphs.
H1 is the conjecture for regular graphs of even degree 2k (k+1 linear forests),
H2 the conjecture for regular graphs of odd degree 2k+1 (k+1 linear forests).
A graph of maximum degree at most D embeds in a D-regular graph: take two copies
of the graph and join the two copies of every vertex of degree below D; this raises
the minimum degree, so finitely many doublings give a D-regular supergraph.
Linear forest decompositions pull back along injective graph homomorphisms.
-/

namespace OMA.R_LinearArboricityConjecture_linear_arboricity_conjecture_R2

open LinearArboricityConjecture

def H1 : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (k : ℕ),
    (∀ w, H.degree w = 2 * k) → HasLinearForestDecomposition H (k + 1)

def H2 : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (k : ℕ),
    (∀ w, H.degree w = 2 * k + 1) → HasLinearForestDecomposition H (k + 1)

lemma ncard_eq_degree {V : Type} (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    (G.neighborSet v).ncard = G.degree v := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

lemma reg_case (h1 : H1) (h2 : H2) {W : Type} [Fintype W] (H : SimpleGraph W) (D : ℕ)
    (hreg : ∀ w, (H.neighborSet w).ncard = D) :
    HasLinearForestDecomposition H ((D + 2) / 2) := by
  classical
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' D
  · have h := h1 W H k (fun w => by rw [← ncard_eq_degree]; exact hreg w)
    rwa [show (2 * k + 2) / 2 = k + 1 by omega]
  · have h := h2 W H k (fun w => by rw [← ncard_eq_degree]; exact hreg w)
    rwa [show (2 * k + 1 + 2) / 2 = k + 1 by omega]

lemma pullback {V W : Type} [Finite W] (G : SimpleGraph V) (G' : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f) (hadj : ∀ u v, G.Adj u v → G'.Adj (f u) (f v)) (k : ℕ)
    (hD : HasLinearForestDecomposition G' k) : HasLinearForestDecomposition G k := by
  obtain ⟨D, hDf, hDe⟩ := hD
  refine ⟨fun i => (D i).comap f ⊓ G, fun i => ⟨⟨?_, ?_⟩, inf_le_right⟩, ?_⟩
  · exact SimpleGraph.IsAcyclic.anti inf_le_left
      (SimpleGraph.IsAcyclic.comap (SimpleGraph.Hom.comap f (D i)) hf (hDf i).1.1)
  · intro v
    refine le_trans (Set.ncard_le_ncard_of_injOn f ?_ hf.injOn) ((hDf i).1.2 (f v))
    intro w hw
    exact hw.1
  · intro u v
    constructor
    · intro h
      obtain ⟨i, hi, huniq⟩ := (hDe (f u) (f v)).mp (hadj u v h)
      exact ⟨i, ⟨hi, h⟩, fun j hj => huniq j hj.1⟩
    · rintro ⟨i, hi, -⟩
      exact hi.2

lemma exists_double {V : Type} [Fintype V] (G : SimpleGraph V) (D : ℕ) :
    ∃ G' : SimpleGraph (V × Bool), (∀ u v, G.Adj u v → G'.Adj (u, false) (v, false)) ∧
      ∀ p : V × Bool, (G'.neighborSet p).ncard =
        if (G.neighborSet p.1).ncard < D then (G.neighborSet p.1).ncard + 1
        else (G.neighborSet p.1).ncard := by
  classical
  refine ⟨{ Adj := fun p q => (p.2 = q.2 ∧ G.Adj p.1 q.1) ∨
              (p.1 = q.1 ∧ p.2 ≠ q.2 ∧ (G.neighborSet p.1).ncard < D),
            symm := ⟨?_⟩, loopless := ⟨?_⟩ }, fun u v h => Or.inl ⟨rfl, h⟩, ?_⟩
  · rintro ⟨a, b⟩ ⟨a', b'⟩ (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · simp only at h1 h2 h3
      subst h1
      exact Or.inr ⟨rfl, Ne.symm h2, h3⟩
  · rintro ⟨a, b⟩ (⟨-, h⟩ | ⟨-, h, -⟩)
    · exact G.irrefl h
    · exact h rfl
  · rintro ⟨v, b⟩
    have himg : ((fun w => (w, b)) '' G.neighborSet v).ncard = (G.neighborSet v).ncard :=
      Set.ncard_image_of_injective _ (fun x y h => congrArg Prod.fst h)
    by_cases hc : (G.neighborSet v).ncard < D
    · rw [if_pos hc, ← himg, ← Set.ncard_insert_of_notMem (a := (v, !b))]
      · congr 1
        ext ⟨w, c⟩
        simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_image,
          Prod.mk.injEq]
        constructor
        · rintro (⟨rfl, h⟩ | ⟨rfl, h, -⟩)
          · exact Or.inr ⟨w, h, rfl, rfl⟩
          · left
            refine ⟨rfl, ?_⟩
            cases b <;> cases c <;> simp_all
        · rintro (⟨rfl, rfl⟩ | ⟨x, h, rfl, rfl⟩)
          · exact Or.inr ⟨rfl, by cases b <;> simp, hc⟩
          · exact Or.inl ⟨rfl, h⟩
      · rintro ⟨x, -, hx⟩
        simp only [Prod.mk.injEq] at hx
        cases b <;> simp at hx
    · rw [if_neg hc, ← himg]
      congr 1
      ext ⟨w, c⟩
      simp only [SimpleGraph.mem_neighborSet, Set.mem_image, Prod.mk.injEq]
      constructor
      · rintro (⟨rfl, h⟩ | ⟨-, -, h⟩)
        · exact ⟨w, h, rfl, rfl⟩
        · exact absurd h hc
      · rintro ⟨x, h, rfl, rfl⟩
        exact Or.inl ⟨rfl, h⟩

lemma bounded_case (h1 : H1) (h2 : H2) (D : ℕ) (m : ℕ) :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (∀ v, (G.neighborSet v).ncard ≤ D) → (∀ v, D ≤ (G.neighborSet v).ncard + m) →
      HasLinearForestDecomposition G ((D + 2) / 2) := by
  induction m with
  | zero =>
    intro V _ G hle hge
    exact reg_case h1 h2 G D fun v => le_antisymm (hle v) (by simpa using hge v)
  | succ m ih =>
    intro V _ G hle hge
    obtain ⟨G', hadj, hdeg⟩ := exists_double G D
    apply pullback G G' (fun v => (v, false)) (fun x y h => congrArg Prod.fst h) hadj
    apply ih (V × Bool) G'
    · rintro ⟨v, b⟩
      rw [hdeg]
      dsimp only
      have := hle v
      split_ifs <;> omega
    · rintro ⟨v, b⟩
      rw [hdeg]
      dsimp only
      have := hge v
      split_ifs <;> omega

theorem main : H1 → H2 → type_of% @LinearArboricityConjecture.linear_arboricity_conjecture := by
  intro h1 h2 V _ G _
  have hD := bounded_case h1 h2 G.maxDegree G.maxDegree V G
    (fun v => by rw [ncard_eq_degree]; exact G.degree_le_maxDegree v) (fun v => by omega)
  unfold linearArboricity
  exact Nat.sInf_le hD

end OMA.R_LinearArboricityConjecture_linear_arboricity_conjecture_R2
