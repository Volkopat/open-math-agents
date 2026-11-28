import OMAReductions.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1_H1_R1
import Mathlib

-- Step Erdos165.erdos_165.variants.conjecture.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction Erdos165.erdos_165.variants.conjecture.R1.H1.R1.H1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Deterministic triangle deletion. Adjacent vertices of `A` (resp. `B`) have distinct first
(resp. second) labels, and the key `q` is injective on pairs of distinct labels, so a triangle of
`A` has a unique edge of largest key; that edge is cut from `C`. Likewise no triangle lies in
`D`. A triangle with two `C` edges and one `D` edge is impossible because the `D` edge has a
cherry in `A` at the third vertex and is cut; symmetrically for two `D` edges and one `C`
edge. Hence `G = C ∪ D` is triangle-free. -/

namespace P4T

theorem q_inj {m : ℕ} {a b c : Fin m} (hab : a ≠ b) (hbc : b ≠ c) :
    min a.val b.val * m + max a.val b.val ≠ min a.val c.val * m + max a.val c.val := by
  intro h
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  have h1 : max a.val b.val < m := max_lt ha hb
  have h2 : max a.val c.val < m := max_lt ha hc
  have e1 := Nat.div_add_mod' (min a.val b.val * m + max a.val b.val) m
  have hd1 : (min a.val b.val * m + max a.val b.val) / m = min a.val b.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h1, zero_add]
  have hd2 : (min a.val c.val * m + max a.val c.val) / m = min a.val c.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h2, zero_add]
  have hm1 : (min a.val b.val * m + max a.val b.val) % m = max a.val b.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
  have hm2 : (min a.val c.val * m + max a.val c.val) % m = max a.val c.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  have emin : min a.val b.val = min a.val c.val := by rw [← hd1, ← hd2, h]
  have emax : max a.val b.val = max a.val c.val := by rw [← hm1, ← hm2, h]
  have hbc' : b.val ≠ c.val := fun e => hbc (Fin.ext e)
  have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
  omega


def qq (m : ℕ) (a b : Fin m) : ℕ := min a.val b.val * m + max a.val b.val

theorem qq_symm (m : ℕ) (a b : Fin m) : qq m a b = qq m b a := by
  unfold qq; rw [min_comm, max_comm]

theorem qq_ne {m : ℕ} {a b c : Fin m} (hab : a ≠ b) (hbc : b ≠ c) : qq m a b ≠ qq m a c :=
  q_inj hab hbc

def dd {V : Type} (m : ℕ) (X Y : SimpleGraph V) (r : V → Fin m) (u v : V) : Prop :=
  (∃ w, X.Adj u v ∧ X.Adj u w ∧ X.Adj v w ∧
    qq m (r u) (r w) < qq m (r u) (r v) ∧ qq m (r v) (r w) < qq m (r u) (r v)) ∨
  (∃ w, Y.Adj w u ∧ Y.Adj w v ∧ X.Adj u v)

def cutG {V : Type} (m : ℕ) (X Y : SimpleGraph V) (r : V → Fin m) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => X.Adj u v ∧ ¬ (dd m X Y r u v ∨ dd m X Y r v u))

theorem cut_adj {V : Type} {m : ℕ} {X Y : SimpleGraph V} {r : V → Fin m} {u v : V}
    (h : (cutG m X Y r).Adj u v) : X.Adj u v ∧ ¬ dd m X Y r u v ∧ ¬ dd m X Y r v u := by
  rw [cutG, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · exact ⟨h1, fun h => h2 (Or.inl h), fun h => h2 (Or.inr h)⟩
  · exact ⟨h1.symm, fun h => h2 (Or.inr h), fun h => h2 (Or.inl h)⟩

theorem no_tri {V : Type} {m : ℕ} {X Y : SimpleGraph V} {r : V → Fin m}
    (hr : ∀ u v, X.Adj u v → r u ≠ r v) {u v w : V}
    (h1 : (cutG m X Y r).Adj u v) (h2 : (cutG m X Y r).Adj u w)
    (h3 : (cutG m X Y r).Adj v w) : False := by
  obtain ⟨a1, n1, n1'⟩ := cut_adj h1
  obtain ⟨a2, n2, n2'⟩ := cut_adj h2
  obtain ⟨a3, n3, n3'⟩ := cut_adj h3
  have duv := hr _ _ a1
  have duw := hr _ _ a2
  have dvw := hr _ _ a3
  have h12 : qq m (r u) (r v) ≠ qq m (r u) (r w) := qq_ne duv dvw
  have h13 : qq m (r u) (r v) ≠ qq m (r v) (r w) := by
    rw [qq_symm m (r u) (r v)]; exact qq_ne duv.symm duw
  have h23 : qq m (r u) (r w) ≠ qq m (r v) (r w) := by
    rw [qq_symm m (r u) (r w), qq_symm m (r v) (r w)]; exact qq_ne duw.symm duv
  have s1 := qq_symm m (r v) (r u)
  have s2 := qq_symm m (r w) (r u)
  have s3 := qq_symm m (r w) (r v)
  rcases lt_or_gt_of_ne h12 with c12 | c12 <;> rcases lt_or_gt_of_ne h13 with c13 | c13 <;>
    rcases lt_or_gt_of_ne h23 with c23 | c23
  all_goals first
    | exact n1 (Or.inl ⟨w, a1, a2, a3, by omega, by omega⟩)
    | exact n2 (Or.inl ⟨v, a2, a1, a3.symm, by omega, by omega⟩)
    | exact n3 (Or.inl ⟨u, a3, a1.symm, a2.symm, by omega, by omega⟩)

theorem mixed {V : Type} {m : ℕ} {X Y : SimpleGraph V} {r r' : V → Fin m} {u v w : V}
    (h1 : (cutG m Y X r').Adj u v) (h2 : (cutG m X Y r).Adj u w)
    (h3 : (cutG m X Y r).Adj v w) : False := by
  obtain ⟨a1, n1, -⟩ := cut_adj h1
  obtain ⟨a2, -, -⟩ := cut_adj h2
  obtain ⟨a3, -, -⟩ := cut_adj h3
  exact n1 (Or.inr ⟨w, a2.symm, a3.symm, a1⟩)

end P4T

open P4T in
theorem OMA.solution : OMA.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1_H1_R1.H2 := by
  intro n m R S f
  show (SimpleGraph.fromRel (fun u v =>
    (cutG m (R.comap (fun v => (f v).1)) (S.comap (fun v => (f v).2)) (fun v => (f v).1)).Adj u v ∨
    (cutG m (S.comap (fun v => (f v).2)) (R.comap (fun v => (f v).1)) (fun v => (f v).2)).Adj u v)).CliqueFree 3
  set A := R.comap (fun v => (f v).1) with hA
  set B := S.comap (fun v => (f v).2) with hB
  have hrA : ∀ u v, A.Adj u v → (f u).1 ≠ (f v).1 := fun u v h => R.ne_of_adj h
  have hrB : ∀ u v, B.Adj u v → (f u).2 ≠ (f v).2 := fun u v h => S.ne_of_adj h
  intro t ht
  rw [SimpleGraph.isNClique_iff, Finset.card_eq_three] at ht
  obtain ⟨hcl, x, y, z, hxy, hxz, hyz, rfl⟩ := ht
  have e : ∀ u v, u ∈ ({x, y, z} : Finset (Fin n)) → v ∈ ({x, y, z} : Finset (Fin n)) → u ≠ v →
      (cutG m A B (fun v => (f v).1)).Adj u v ∨ (cutG m B A (fun v => (f v).2)).Adj u v := by
    intro u v hu hv huv
    have h := hcl hu hv huv
    rw [SimpleGraph.fromRel_adj] at h
    rcases h with ⟨-, (h | h) | (h | h)⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  rcases e x y (by simp) (by simp) hxy with c1 | c1 <;>
    rcases e x z (by simp) (by simp) hxz with c2 | c2 <;>
    rcases e y z (by simp) (by simp) hyz with c3 | c3
  · exact no_tri hrA c1 c2 c3
  · exact mixed c3 c1.symm c2.symm
  · exact mixed c2 c1 c3.symm
  · exact mixed c1 c2 c3
  · exact mixed c1 c2 c3
  · exact mixed c2 c1 c3.symm
  · exact mixed c3 c1.symm c2.symm
  · exact no_tri hrB c1 c2 c3
