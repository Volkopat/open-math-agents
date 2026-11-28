import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1
import Mathlib

/-!
# Proof of `Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H1.R1.H2.R1.H1`

Every abelian voltage graph over a finite abelian base `B` with three distinct shifts `{0, a, b}`
contains a simple cycle of length 4, 8, 16, or 32.
-/

namespace Erdos64H1Proof

open SimpleGraph Finset
open OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1

/- ## Section 0: Normalized graph, basic cycle constructors, and S_3 symmetries -/

/-- The normalized voltage graph on `Bool × B × V` where shift `0` has voltage `0`,
shift `a` has voltage `x i`, and shift `b` has voltage `y i`. -/
def GNorm {B V : Type*} [AddCommGroup B] [AddCommGroup V]
    (a b : B) (x y : B → V) : SimpleGraph (Bool × B × V) :=
  SimpleGraph.fromRel fun l r =>
    ∃ (i : B) (g : V),
      l = (false, i, g) ∧
        (r = (true, i, g) ∨ r = (true, i + a, g + x i) ∨ r = (true, i + b, g + y i))

/-- Goal shorthand: `G` contains a 4-, 8-, 16-, or 32-cycle. -/
def HasPow2 {X : Type*} (G : SimpleGraph X) : Prop :=
  cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G

lemma hasPow2_of_4 {X : Type*} {G : SimpleGraph X} (h : cycleGraph 4 ⊑ G) : HasPow2 G :=
  .inl h
lemma hasPow2_of_8 {X : Type*} {G : SimpleGraph X} (h : cycleGraph 8 ⊑ G) : HasPow2 G :=
  .inr (.inl h)
lemma hasPow2_of_16 {X : Type*} {G : SimpleGraph X} (h : cycleGraph 16 ⊑ G) : HasPow2 G :=
  .inr (.inr (.inl h))
lemma hasPow2_of_32 {X : Type*} {G : SimpleGraph X} (h : cycleGraph 32 ⊑ G) : HasPow2 G :=
  .inr (.inr (.inr h))

lemma hasPow2_of_4_8_16 {X : Type*} {G : SimpleGraph X}
    (h : cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) : HasPow2 G := by
  rcases h with h | h | h
  · exact hasPow2_of_4 h
  · exact hasPow2_of_8 h
  · exact hasPow2_of_16 h

lemma hasPow2_mono {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (hGH : G ⊑ H) (h : HasPow2 G) : HasPow2 H := by
  rcases h with h | h | h | h
  · exact hasPow2_of_4 (h.trans hGH)
  · exact hasPow2_of_8 (h.trans hGH)
  · exact hasPow2_of_16 (h.trans hGH)
  · exact hasPow2_of_32 (h.trans hGH)

section NormBasic
variable {B V : Type*} [AddCommGroup B] [AddCommGroup V]
variable {a b : B} {x y : B → V}

lemma e0 (i : B) (g : V) : (GNorm a b x y).Adj (false, i, g) (true, i, g) :=
  ⟨by simp, .inl ⟨i, g, rfl, .inl rfl⟩⟩

lemma ea (i : B) (g : V) : (GNorm a b x y).Adj (false, i, g) (true, i + a, g + x i) :=
  ⟨by simp, .inl ⟨i, g, rfl, .inr (.inl rfl)⟩⟩

lemma eb (i : B) (g : V) : (GNorm a b x y).Adj (false, i, g) (true, i + b, g + y i) :=
  ⟨by simp, .inl ⟨i, g, rfl, .inr (.inr rfl)⟩⟩

lemma e0' (i : B) (g : V) : (GNorm a b x y).Adj (true, i, g) (false, i, g) :=
  (e0 i g).symm

lemma ea' (i : B) (g : V) : (GNorm a b x y).Adj (true, i + a, g + x i) (false, i, g) :=
  (ea i g).symm

lemma eb' (i : B) (g : V) : (GNorm a b x y).Adj (true, i + b, g + y i) (false, i, g) :=
  (eb i g).symm

lemma ea_sub (i : B) (g : V) : (GNorm a b x y).Adj (true, i + a, g) (false, i, g - x i) := by
  have h := ea' (a := a) (b := b) (x := x) (y := y) i (g - x i); rwa [sub_add_cancel] at h

lemma eb_sub (i : B) (g : V) : (GNorm a b x y).Adj (true, i + b, g) (false, i, g - y i) := by
  have h := eb' (a := a) (b := b) (x := x) (y := y) i (g - y i); rwa [sub_add_cancel] at h

lemma adj_shift {s1 s2 : Bool} {i1 i2 : B} {g1 g2 : V}
    (h : (GNorm a b x y).Adj (s1, i1, g1) (s2, i2, g2)) (d : V) :
    (GNorm a b x y).Adj (s1, i1, g1 + d) (s2, i2, g2 + d) := by
  rcases h with ⟨_, hr | hr⟩
  · rcases hr with ⟨i, g, h1, h2 | h2 | h2⟩
    · simp only [Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨rfl, rfl, rfl⟩; rcases h2 with ⟨rfl, rfl, rfl⟩
      exact e0 i2 (g2 + d)
    · simp only [Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨rfl, rfl, rfl⟩; rcases h2 with ⟨rfl, rfl, rfl⟩
      simpa [add_right_comm] using ea (a := a) (b := b) (x := x) (y := y) i1 (g1 + d)
    · simp only [Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨rfl, rfl, rfl⟩; rcases h2 with ⟨rfl, rfl, rfl⟩
      simpa [add_right_comm] using eb (a := a) (b := b) (x := x) (y := y) i1 (g1 + d)
  · rcases hr with ⟨i, g, h1, h2 | h2 | h2⟩
    · simp only [Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨rfl, rfl, rfl⟩; rcases h2 with ⟨rfl, rfl, rfl⟩
      exact e0' i1 (g1 + d)
    · simp only [Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨rfl, rfl, rfl⟩; rcases h2 with ⟨rfl, rfl, rfl⟩
      simpa [add_right_comm] using ea' (a := a) (b := b) (x := x) (y := y) i2 (g2 + d)
    · simp only [Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨rfl, rfl, rfl⟩; rcases h2 with ⟨rfl, rfl, rfl⟩
      simpa [add_right_comm] using eb' (a := a) (b := b) (x := x) (y := y) i2 (g2 + d)

/-- Any closed injective walk of length `n ≥ 3` yields `cycleGraph n ⊑ G`. -/
lemma walk_to_cycle {X : Type*} {G : SimpleGraph X} {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (f : Fin n → X) (hinj : Function.Injective f)
    (hstep : ∀ i : Fin n, G.Adj (f i) (f (i + 1))) :
    cycleGraph n ⊑ G := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro i j hij
  rw [SimpleGraph.cycleGraph_adj] at hij
  rcases hij with h | h
  · have : i = j + 1 := (sub_eq_iff_eq_add.mp h).trans (add_comm 1 j)
    rw [this]
    exact (hstep j).symm
  · have : j = i + 1 := (sub_eq_iff_eq_add.mp h).trans (add_comm 1 i)
    rw [this]
    exact hstep i

/-- Gauge-fixing: reduce the original `w : B → Fin 3 → V` graph to `GNorm`. -/
lemma gnorm_le_orig (a b : B) (w : B → Fin 3 → V) :
    GNorm a b (fun i => w i 1 - w (i + a) 0) (fun i => w i 2 - w (i + b) 0) ⊑
      SimpleGraph.fromRel (fun l r : Bool × B × V =>
        ∃ (i : B) (k : Fin 3) (g : V),
          l = (false, i, g) ∧ r = (true, i + (![0, a, b] : Fin 3 → B) k, g + w i k)) := by
  let emb : (Bool × B × V) ↪ (Bool × B × V) :=
    { toFun := fun z => (z.1, z.2.1, z.2.2 + if z.1 then w z.2.1 0 else 0)
      inj' := by
        rintro ⟨s1, i1, g1⟩ ⟨s2, i2, g2⟩ h
        simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, hg⟩
        exact Prod.ext rfl (Prod.ext rfl (add_right_cancel hg)) }
  refine ⟨⟨⟨emb, ?_⟩, emb.injective⟩⟩
  have fwd : ∀ i g,
      (SimpleGraph.fromRel fun l r : Bool × B × V =>
        ∃ (i : B) (k : Fin 3) (g : V),
          l = (false, i, g) ∧ r = (true, i + (![0, a, b] : Fin 3 → B) k, g + w i k)).Adj
        (emb (false, i, g)) (emb (true, i, g)) := fun i g =>
    ⟨by simp [emb], .inl ⟨i, 0, g,
      by change (false, i, g + 0) = (false, i, g); simp,
      by change (true, i, g + w i 0) = (true, i + 0, g + w i 0); simp⟩⟩
  have fwda : ∀ i g,
      (SimpleGraph.fromRel fun l r : Bool × B × V =>
        ∃ (i : B) (k : Fin 3) (g : V),
          l = (false, i, g) ∧ r = (true, i + (![0, a, b] : Fin 3 → B) k, g + w i k)).Adj
        (emb (false, i, g)) (emb (true, i + a, g + (w i 1 - w (i + a) 0))) := fun i g =>
    ⟨by simp [emb], .inl ⟨i, 1, g,
      by change (false, i, g + 0) = (false, i, g); simp,
      by change (true, i + a, g + (w i 1 - w (i + a) 0) + w (i + a) 0) = (true, i + a, g + w i 1)
         simp [add_assoc, sub_add_cancel]⟩⟩
  have fwdb : ∀ i g,
      (SimpleGraph.fromRel fun l r : Bool × B × V =>
        ∃ (i : B) (k : Fin 3) (g : V),
          l = (false, i, g) ∧ r = (true, i + (![0, a, b] : Fin 3 → B) k, g + w i k)).Adj
        (emb (false, i, g)) (emb (true, i + b, g + (w i 2 - w (i + b) 0))) := fun i g =>
    ⟨by simp [emb], .inl ⟨i, 2, g,
      by change (false, i, g + 0) = (false, i, g); simp,
      by change (true, i + b, g + (w i 2 - w (i + b) 0) + w (i + b) 0) = (true, i + b, g + w i 2)
         simp [add_assoc, sub_add_cancel]⟩⟩
  intro u v huv
  rcases huv with ⟨_, hr | hr⟩
  · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
    · exact fwd i g
    · exact fwda i g
    · exact fwdb i g
  · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
    · exact (fwd i g).symm
    · exact (fwda i g).symm
    · exact (fwdb i g).symm

/-- `S_3` symmetry 1: swap `a ↔ b` and `x ↔ y`. -/
lemma gnorm_swap_ab : GNorm b a y x ⊑ GNorm a b x y := by
  refine ⟨⟨⟨id, ?_⟩, Function.injective_id⟩⟩
  intro u v huv
  rcases huv with ⟨_, hr | hr⟩
  · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
    · exact e0 i g
    · exact eb i g
    · exact ea i g
  · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
    · exact e0' i g
    · exact eb' i g
    · exact ea' i g

/-- `S_3` symmetry 2: swap `0 ↔ a`, replacing `(a, b)` by `(-a, b - a)`. -/
lemma gnorm_swap_0a :
    GNorm (-a) (b - a) (fun i => -x (i - a)) (fun i => y i - x (i + b - a)) ⊑ GNorm a b x y := by
  let emb : (Bool × B × V) ↪ (Bool × B × V) :=
    { toFun := fun z =>
        if z.1 then (true, z.2.1 + a, z.2.2 + x z.2.1) else (false, z.2.1, z.2.2)
      inj' := by
        rintro ⟨s1, i1, g1⟩ ⟨s2, i2, g2⟩ h
        cases s1 <;> cases s2 <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
        · exact Prod.ext rfl (Prod.ext h.2.1 h.2.2)
        · exact False.elim (absurd h.1 (by decide))
        · exact False.elim (absurd h.1 (by decide))
        · have hi : i1 = i2 := add_right_cancel h.2.1
          subst hi
          exact Prod.ext rfl (Prod.ext rfl (add_right_cancel h.2.2)) }
  refine ⟨⟨⟨emb, ?_⟩, emb.injective⟩⟩
  have f0 : ∀ i g, (GNorm a b x y).Adj (emb (false, i, g)) (emb (true, i, g)) :=
    fun i g => ea i g
  have fa : ∀ i g, (GNorm a b x y).Adj (emb (false, i, g))
      (emb (true, i + (-a), g + (-x (i - a)))) := by
    intro i g
    have h1 : i + (-a) + a = i := by abel
    have h2 : g + -x (i - a) + x (i + -a) = g := by
      rw [show i + -a = i - a from (sub_eq_add_neg i a).symm]; abel
    change (GNorm a b x y).Adj (false, i, g) (true, i + (-a) + a, g + (-x (i - a)) + x (i + (-a)))
    rw [h1, h2]
    exact e0 i g
  have fb : ∀ i g, (GNorm a b x y).Adj (emb (false, i, g))
      (emb (true, i + (b - a), g + (y i - x (i + b - a)))) := by
    intro i g
    have h1 : i + (b - a) + a = i + b := by abel
    have h2 : g + (y i - x (i + b - a)) + x (i + (b - a)) = g + y i := by
      rw [show i + (b - a) = i + b - a by abel]; abel
    change (GNorm a b x y).Adj (false, i, g)
      (true, i + (b - a) + a, g + (y i - x (i + b - a)) + x (i + (b - a)))
    rw [h1, h2]
    exact eb i g
  intro u v huv
  rcases huv with ⟨_, hr | hr⟩
  · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
    · exact f0 i g
    · exact fa i g
    · exact fb i g
  · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
    · exact (f0 i g).symm
    · exact (fa i g).symm
    · exact (fb i g).symm

/-- Translation symmetry in `B`: shift all base coordinates by `s`. -/
lemma gnorm_translate (s : B) :
    GNorm a b (fun i => x (i + s)) (fun i => y (i + s)) ⊑ GNorm a b x y := by
  let emb : (Bool × B × V) ↪ (Bool × B × V) :=
    { toFun := fun z => (z.1, z.2.1 + s, z.2.2)
      inj' := by
        rintro ⟨s1, i1, g1⟩ ⟨s2, i2, g2⟩ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Prod.ext (add_right_cancel h.2.1) h.2.2) }
  refine ⟨⟨⟨emb, ?_⟩, emb.injective⟩⟩
  intro u v huv
  rcases huv with ⟨_, hr | hr⟩
  · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
    · exact e0 (i + s) g
    · change (GNorm a b x y).Adj (false, i + s, g) (true, i + a + s, g + x (i + s))
      rw [add_right_comm]; exact ea (i + s) g
    · change (GNorm a b x y).Adj (false, i + s, g) (true, i + b + s, g + y (i + s))
      rw [add_right_comm]; exact eb (i + s) g
  · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
    · exact e0' (i + s) g
    · change (GNorm a b x y).Adj (true, i + a + s, g + x (i + s)) (false, i + s, g)
      rw [add_right_comm]; exact ea' (i + s) g
    · change (GNorm a b x y).Adj (true, i + b + s, g + y (i + s)) (false, i + s, g)
      rw [add_right_comm]; exact eb' (i + s) g

/-- Hexagon voltage at `i : B`. -/
def hexV (a b : B) (x y : B → V) (i : B) : V :=
  x i + y (i + a) - x (i + b) - y i

/-- Connection to `LocalCommutation.near0..3`: if `hexV i = 0` and at least 3 of its
4 cardinal neighbors `i ± a, i ± b` have `hexV = 0`, then `HasPow2`. -/
lemma local_comm_bound [DecidableEq V] (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hno : ¬ HasPow2 (GNorm a b x y)) (i : B) (hi : hexV a b x y i = 0) :
    2 ≤ (if hexV a b x y (i + a) ≠ 0 then 1 else 0) +
        (if hexV a b x y (i - a) ≠ 0 then 1 else 0) +
        (if hexV a b x y (i + b) ≠ 0 then 1 else 0) +
        (if hexV a b x y (i - b) ≠ 0 then 1 else 0) := by
  let p : Equiv.Perm (B × V) :=
    { toFun := fun z => (z.1 + a, z.2 + x z.1)
      invFun := fun z => (z.1 - a, z.2 - x (z.1 - a))
      left_inv := fun ⟨j, g⟩ => by simp
      right_inv := fun ⟨j, g⟩ => by simp }
  let q : Equiv.Perm (B × V) :=
    { toFun := fun z => (z.1 + b, z.2 + y z.1)
      invFun := fun z => (z.1 - b, z.2 - y (z.1 - b))
      left_inv := fun ⟨j, g⟩ => by simp
      right_inv := fun ⟨j, g⟩ => by simp }
  have sep : ∀ z : B × V, p z ≠ z ∧ q z ≠ z ∧ p z ≠ q z := by
    rintro ⟨j, g⟩
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact ha (by simpa [p] using congrArg Prod.fst h)
    · intro h; exact hb (by simpa [q] using congrArg Prod.fst h)
    · intro h; exact hab (by simpa [p, q] using congrArg Prod.fst h)
  have idAdj : ∀ z : B × V, (GNorm a b x y).Adj (false, z) (true, z) :=
    fun ⟨j, g⟩ => e0 j g
  have pAdj : ∀ z : B × V, (GNorm a b x y).Adj (false, z) (true, p z) :=
    fun ⟨j, g⟩ => ea j g
  have qAdj : ∀ z : B × V, (GNorm a b x y).Adj (false, z) (true, q z) :=
    fun ⟨j, g⟩ => eb j g
  have comm_of : ∀ (j : B) (g : V), hexV a b x y j = 0 → p (q (j, g)) = q (p (j, g)) := by
    intro j g hj
    apply Prod.ext
    · change j + b + a = j + a + b; abel
    · change g + y j + x (j + b) = g + x j + y (j + a)
      dsimp [hexV] at hj
      linear_combination (norm := abel) -hj
  have c_center : p (q (i, (0 : V))) = q (p (i, (0 : V))) := comm_of i 0 hi
  have c_p : hexV a b x y (i + a) = 0 → p (q (p (i, (0 : V)))) = q (p (p (i, (0 : V)))) :=
    fun h => comm_of (i + a) _ h
  have c_ps : hexV a b x y (i - a) = 0 →
      p (q (p.symm (i, (0 : V)))) = q (p (p.symm (i, (0 : V)))) :=
    fun h => comm_of (i - a) _ h
  have c_q : hexV a b x y (i + b) = 0 → p (q (q (i, (0 : V)))) = q (p (q (i, (0 : V)))) :=
    fun h => comm_of (i + b) _ h
  have c_qs : hexV a b x y (i - b) = 0 →
      p (q (q.symm (i, (0 : V)))) = q (p (q.symm (i, (0 : V)))) :=
    fun h => comm_of (i - b) _ h
  by_cases hpa : hexV a b x y (i + a) = 0
  · by_cases hma : hexV a b x y (i - a) = 0
    · by_cases hpb : hexV a b x y (i + b) = 0
      · exact False.elim (hno (hasPow2_of_4_8_16 (LocalCommutation.near2 _ p q sep idAdj pAdj qAdj
          (i, 0) c_center (c_ps hma) (c_p hpa) (c_q hpb))))
      · by_cases hmb : hexV a b x y (i - b) = 0
        · exact False.elim (hno (hasPow2_of_4_8_16 (LocalCommutation.near3 _ p q sep idAdj pAdj qAdj
            (i, 0) c_center (c_ps hma) (c_p hpa) (c_qs hmb))))
        · simp [hpa, hma, hpb, hmb]
    · by_cases hpb : hexV a b x y (i + b) = 0
      · by_cases hmb : hexV a b x y (i - b) = 0
        · exact False.elim (hno (hasPow2_of_4_8_16 (LocalCommutation.near0 _ p q sep idAdj pAdj qAdj
            (i, 0) c_center (c_p hpa) (c_qs hmb) (c_q hpb))))
        · simp [hpa, hma, hpb, hmb]
      · simp [hpa, hma, hpb]
  · by_cases hma : hexV a b x y (i - a) = 0
    · by_cases hpb : hexV a b x y (i + b) = 0
      · by_cases hmb : hexV a b x y (i - b) = 0
        · exact False.elim (hno (hasPow2_of_4_8_16 (LocalCommutation.near1 _ p q sep idAdj pAdj qAdj
            (i, 0) c_center (c_ps hma) (c_qs hmb) (c_q hpb))))
        · simp [hpa, hma, hpb, hmb]
      · simp [hpa, hma, hpb]
    · by_cases hpb : hexV a b x y (i + b) = 0 <;> by_cases hmb : hexV a b x y (i - b) = 0 <;>
        simp [hpa, hma, hpb, hmb]

/-- If `hexV = 0` everywhere, `HasPow2` holds immediately. -/
lemma hasPow2_of_all_hexV_zero (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hall : ∀ i : B, hexV a b x y i = 0) : HasPow2 (GNorm a b x y) := by
  classical
  by_contra hno
  have h := local_comm_bound ha hb hab hno 0 (hall 0)
  simp [hall] at h

end NormBasic

/- ## Section 1: Abstract Reusable Walk Lemmas (Barbell & Theta) -/

section WalkEngines
variable {B V : Type*} [AddCommGroup B] [AddCommGroup V]
variable {a b : B} {x y : B → V}

omit [AddCommGroup B] in
/-- Fast injectivity helper for walks indexed by `(idx i : Fin m, off i : V)` over an injective
base map `u : Fin m → Bool × B`: reduces `n × n` injectivity to just checking `off i ≠ off j`
on the explicit list `cols` of pairs `(i, j)` with `i < j` and `idx i = idx j`! -/
lemma walk_inj_of_cols {α : Type*} [DecidableEq α] {n : ℕ}
    (u : α → Bool × B) (hu : Function.Injective u)
    (w : Fin n → α) (gv : Fin n → V) (cols : List (Fin n × Fin n))
    (hcols : ∀ i j : Fin n, i < j → w i = w j → (i, j) ∈ cols)
    (hdiff : ∀ p ∈ cols, gv p.1 ≠ gv p.2) :
    Function.Injective (fun k : Fin n => ((u (w k)).1, (u (w k)).2, gv k)) := by
  intro i j hij
  by_contra hne
  have hw : w i = w j := hu (Prod.ext (congrArg (fun z : Bool × B × V => z.1) hij)
    (congrArg (fun z : Bool × B × V => z.2.1) hij))
  have hg : gv i = gv j := congrArg (fun z : Bool × B × V => z.2.2) hij
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hdiff (i, j) (hcols i j hlt hw) hg
  · exact hdiff (j, i) (hcols j i hgt hw.symm) hg.symm

lemma indexed_walk_inj {m n : ℕ} (u : Fin m → Bool × B) (hu : Function.Injective u)
    (g : Fin m → V) (idx : Fin n → Fin m) (off : Fin n → V)
    (cols : List (Fin n × Fin n))
    (hcols : ∀ i j : Fin n, i < j → idx i = idx j → (i, j) ∈ cols)
    (hdiff : ∀ p ∈ cols, off p.1 ≠ off p.2) :
    Function.Injective (fun i : Fin n => ((u (idx i)).1, (u (idx i)).2, g (idx i) + off i)) := by
  intro i j hij
  by_contra hne
  have hk : idx i = idx j :=
    hu (Prod.ext (congrArg (fun z : Bool × B × V => z.1) hij)
                 (congrArg (fun z : Bool × B × V => z.2.1) hij))
  have hg : g (idx i) + off i = g (idx j) + off j :=
    congrArg (fun z : Bool × B × V => z.2.2) hij
  rw [hk] at hg
  have hoff : off i = off j := add_left_cancel hg
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hdiff (i, j) (hcols i j hlt hk) hoff
  · exact hdiff (j, i) (hcols j i hlt hk.symm) hoff.symm

/-- Barbell `(6, 2, 6)`: two base 6-cycles `C1, C2` with voltages `v1, v2`, connected by a
base 2-path `0 -- 6 -- 7`, all 13 base vertices distinct.
If `v1 ≠ 0` and `v2 ≠ 0`, then `cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G`. -/
lemma barbell_6_2_6
    (u : Fin 13 → Bool × B) (hu : Function.Injective u)
    (g : Fin 13 → V) (v1 v2 : V) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0)
    (hc1_0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 1 |>.1, u 1 |>.2, g 1))
    (hc1_1 : (GNorm a b x y).Adj (u 1 |>.1, u 1 |>.2, g 1) (u 2 |>.1, u 2 |>.2, g 2))
    (hc1_2 : (GNorm a b x y).Adj (u 2 |>.1, u 2 |>.2, g 2) (u 3 |>.1, u 3 |>.2, g 3))
    (hc1_3 : (GNorm a b x y).Adj (u 3 |>.1, u 3 |>.2, g 3) (u 4 |>.1, u 4 |>.2, g 4))
    (hc1_4 : (GNorm a b x y).Adj (u 4 |>.1, u 4 |>.2, g 4) (u 5 |>.1, u 5 |>.2, g 5))
    (hc1_5 : (GNorm a b x y).Adj (u 5 |>.1, u 5 |>.2, g 5) (u 0 |>.1, u 0 |>.2, g 0 + v1))
    (hb_0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 6 |>.1, u 6 |>.2, g 6))
    (hb_1 : (GNorm a b x y).Adj (u 6 |>.1, u 6 |>.2, g 6) (u 7 |>.1, u 7 |>.2, g 7))
    (hc2_0 : (GNorm a b x y).Adj (u 7 |>.1, u 7 |>.2, g 7) (u 8 |>.1, u 8 |>.2, g 8))
    (hc2_1 : (GNorm a b x y).Adj (u 8 |>.1, u 8 |>.2, g 8) (u 9 |>.1, u 9 |>.2, g 9))
    (hc2_2 : (GNorm a b x y).Adj (u 9 |>.1, u 9 |>.2, g 9) (u 10 |>.1, u 10 |>.2, g 10))
    (hc2_3 : (GNorm a b x y).Adj (u 10 |>.1, u 10 |>.2, g 10) (u 11 |>.1, u 11 |>.2, g 11))
    (hc2_4 : (GNorm a b x y).Adj (u 11 |>.1, u 11 |>.2, g 11) (u 12 |>.1, u 12 |>.2, g 12))
    (hc2_5 : (GNorm a b x y).Adj (u 12 |>.1, u 12 |>.2, g 12) (u 7 |>.1, u 7 |>.2, g 7 + v2)) :
    HasPow2 (GNorm a b x y) := by
  let pt (k : Fin 13) (d : V) : Bool × B × V := ((u k).1, (u k).2, g k + d)
  have st : ∀ {k1 k2 : Fin 13} {d1 d2 : V},
      (GNorm a b x y).Adj (u k1 |>.1, u k1 |>.2, g k1) (u k2 |>.1, u k2 |>.2, g k2) →
      d1 = d2 → (GNorm a b x y).Adj (pt k1 d1) (pt k2 d2) := by
    intro k1 k2 d1 d2 hadj hd; subst hd; exact adj_shift hadj d1
  have st_end1 : ∀ d1 d2, d2 = d1 + v1 → (GNorm a b x y).Adj (pt 5 d1) (pt 0 d2) := by
    intro d1 d2 hd; subst hd
    simpa [pt, add_assoc, add_comm, add_left_comm] using adj_shift hc1_5 d1
  have st_end2 : ∀ d1 d2, d2 = d1 + v2 → (GNorm a b x y).Adj (pt 12 d1) (pt 7 d2) := by
    intro d1 d2 hd; subst hd
    simpa [pt, add_assoc, add_comm, add_left_comm] using adj_shift hc2_5 d1
  by_cases hsum : v1 + v2 = 0
  · let idx : Fin 16 → Fin 13 := ![0, 1, 2, 3, 4, 5, 0, 6, 7, 8, 9, 10, 11, 12, 7, 6]
    let off : Fin 16 → V := ![0, 0, 0, 0, 0, 0, v1, v1, v1, v1, v1, v1, v1, v1, 0, 0]
    let f : Fin 16 → Bool × B × V := fun i => pt (idx i) (off i)
    apply hasPow2_of_16 (walk_to_cycle (by decide) f ?_ ?_)
    · refine indexed_walk_inj u hu g idx off [(0, 6), (7, 15), (8, 14)] (by decide) ?_
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> dsimp [off]
      · exact hv1.symm
      · exact hv1
      · exact hv1
    · intro i; fin_cases i <;> dsimp [f, idx, off]
      · exact st hc1_0 rfl
      · exact st hc1_1 rfl
      · exact st hc1_2 rfl
      · exact st hc1_3 rfl
      · exact st hc1_4 rfl
      · exact st_end1 0 v1 (by abel)
      · exact st hb_0 rfl
      · exact st hb_1 rfl
      · exact st hc2_0 rfl
      · exact st hc2_1 rfl
      · exact st hc2_2 rfl
      · exact st hc2_3 rfl
      · exact st hc2_4 rfl
      · exact st_end2 v1 0 (by linear_combination (norm := abel) -hsum)
      · exact (st hb_1 rfl).symm
      · exact (st hb_0 rfl).symm
  · by_cases hdiff : v1 - v2 = 0
    · let idx : Fin 16 → Fin 13 := ![0, 1, 2, 3, 4, 5, 0, 6, 7, 12, 11, 10, 9, 8, 7, 6]
      let off : Fin 16 → V := ![0, 0, 0, 0, 0, 0, v1, v1, v1, 0, 0, 0, 0, 0, 0, 0]
      let f : Fin 16 → Bool × B × V := fun i => pt (idx i) (off i)
      apply hasPow2_of_16 (walk_to_cycle (by decide) f ?_ ?_)
      · refine indexed_walk_inj u hu g idx off [(0, 6), (7, 15), (8, 14)] (by decide) ?_
        intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> dsimp [off]
        · exact hv1.symm
        · exact hv1
        · exact hv1
      · intro i; fin_cases i <;> dsimp [f, idx, off]
        · exact st hc1_0 rfl
        · exact st hc1_1 rfl
        · exact st hc1_2 rfl
        · exact st hc1_3 rfl
        · exact st hc1_4 rfl
        · exact st_end1 0 v1 (by abel)
        · exact st hb_0 rfl
        · exact st hb_1 rfl
        · exact (st_end2 0 v1 (by linear_combination (norm := abel) hdiff)).symm
        · exact (st hc2_4 rfl).symm
        · exact (st hc2_3 rfl).symm
        · exact (st hc2_2 rfl).symm
        · exact (st hc2_1 rfl).symm
        · exact (st hc2_0 rfl).symm
        · exact (st hb_1 rfl).symm
        · exact (st hb_0 rfl).symm
    · let idx : Fin 32 → Fin 13 := ![
        0, 1, 2, 3, 4, 5, 0, 6, 7, 8, 9, 10, 11, 12, 7, 6,
        0, 5, 4, 3, 2, 1, 0, 6, 7, 12, 11, 10, 9, 8, 7, 6]
      let off : Fin 32 → V := ![
        0, 0, 0, 0, 0, 0, v1, v1, v1, v1, v1, v1, v1, v1, v1 + v2, v1 + v2,
        v1 + v2, v2, v2, v2, v2, v2, v2, v2, v2, 0, 0, 0, 0, 0, 0, 0]
      let f : Fin 32 → Bool × B × V := fun i => pt (idx i) (off i)
      apply hasPow2_of_32 (walk_to_cycle (by decide) f ?_ ?_)
      · refine indexed_walk_inj u hu g idx off
          [(0, 6), (0, 16), (0, 22), (6, 16), (6, 22), (16, 22),
           (1, 21), (2, 20), (3, 19), (4, 18), (5, 17),
           (7, 15), (7, 23), (7, 31), (15, 23), (15, 31), (23, 31),
           (8, 14), (8, 24), (8, 30), (14, 24), (14, 30), (24, 30),
           (9, 29), (10, 28), (11, 27), (12, 26), (13, 25)] (by decide) ?_
        intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp [off] <;>
          intro e <;> first
            | (solve | apply hv1; linear_combination (norm := abel) e)
            | (solve | apply hv1; linear_combination (norm := abel) -e)
            | (solve | apply hv2; linear_combination (norm := abel) e)
            | (solve | apply hv2; linear_combination (norm := abel) -e)
            | (solve | apply hsum; linear_combination (norm := abel) e)
            | (solve | apply hsum; linear_combination (norm := abel) -e)
            | (solve | apply hdiff; linear_combination (norm := abel) e)
      · intro i; fin_cases i <;> dsimp [f, idx, off]
        · exact st hc1_0 rfl
        · exact st hc1_1 rfl
        · exact st hc1_2 rfl
        · exact st hc1_3 rfl
        · exact st hc1_4 rfl
        · exact st_end1 0 v1 (by abel)
        · exact st hb_0 rfl
        · exact st hb_1 rfl
        · exact st hc2_0 rfl
        · exact st hc2_1 rfl
        · exact st hc2_2 rfl
        · exact st hc2_3 rfl
        · exact st hc2_4 rfl
        · exact st_end2 v1 (v1 + v2) (by abel)
        · exact (st hb_1 rfl).symm
        · exact (st hb_0 rfl).symm
        · exact (st_end1 v2 (v1 + v2) (by abel)).symm
        · exact (st hc1_4 rfl).symm
        · exact (st hc1_3 rfl).symm
        · exact (st hc1_2 rfl).symm
        · exact (st hc1_1 rfl).symm
        · exact (st hc1_0 rfl).symm
        · exact st hb_0 rfl
        · exact st hb_1 rfl
        · exact (st_end2 0 v2 (by abel)).symm
        · exact (st hc2_4 rfl).symm
        · exact (st hc2_3 rfl).symm
        · exact (st hc2_2 rfl).symm
        · exact (st hc2_1 rfl).symm
        · exact (st hc2_0 rfl).symm
        · exact (st hb_1 rfl).symm
        · exact (st hb_0 rfl).symm

/-- Barbell `(4, 4, 4)`: two base 4-cycles `C1, C2` with voltages `v1, v2`, connected by a
base 4-path `0 -> 4 -> 5 -> 6 -> 7`, all 11 base vertices distinct. -/
lemma barbell_4_4_4
    (u : Fin 11 → Bool × B) (hu : Function.Injective u)
    (g : Fin 11 → V) (v1 v2 : V) (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0)
    (hc1_0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 1 |>.1, u 1 |>.2, g 1))
    (hc1_1 : (GNorm a b x y).Adj (u 1 |>.1, u 1 |>.2, g 1) (u 2 |>.1, u 2 |>.2, g 2))
    (hc1_2 : (GNorm a b x y).Adj (u 2 |>.1, u 2 |>.2, g 2) (u 3 |>.1, u 3 |>.2, g 3))
    (hc1_3 : (GNorm a b x y).Adj (u 3 |>.1, u 3 |>.2, g 3) (u 0 |>.1, u 0 |>.2, g 0 + v1))
    (hb_0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 4 |>.1, u 4 |>.2, g 4))
    (hb_1 : (GNorm a b x y).Adj (u 4 |>.1, u 4 |>.2, g 4) (u 5 |>.1, u 5 |>.2, g 5))
    (hb_2 : (GNorm a b x y).Adj (u 5 |>.1, u 5 |>.2, g 5) (u 6 |>.1, u 6 |>.2, g 6))
    (hb_3 : (GNorm a b x y).Adj (u 6 |>.1, u 6 |>.2, g 6) (u 7 |>.1, u 7 |>.2, g 7))
    (hc2_0 : (GNorm a b x y).Adj (u 7 |>.1, u 7 |>.2, g 7) (u 8 |>.1, u 8 |>.2, g 8))
    (hc2_1 : (GNorm a b x y).Adj (u 8 |>.1, u 8 |>.2, g 8) (u 9 |>.1, u 9 |>.2, g 9))
    (hc2_2 : (GNorm a b x y).Adj (u 9 |>.1, u 9 |>.2, g 9) (u 10 |>.1, u 10 |>.2, g 10))
    (hc2_3 : (GNorm a b x y).Adj (u 10 |>.1, u 10 |>.2, g 10) (u 7 |>.1, u 7 |>.2, g 7 + v2)) :
    HasPow2 (GNorm a b x y) := by
  let pt (k : Fin 11) (d : V) : Bool × B × V := ((u k).1, (u k).2, g k + d)
  have st : ∀ {k1 k2 : Fin 11} {d1 d2 : V},
      (GNorm a b x y).Adj (u k1 |>.1, u k1 |>.2, g k1) (u k2 |>.1, u k2 |>.2, g k2) →
      d1 = d2 → (GNorm a b x y).Adj (pt k1 d1) (pt k2 d2) := by
    intro k1 k2 d1 d2 hadj hd; subst hd; exact adj_shift hadj d1
  have st_end1 : ∀ d1 d2, d2 = d1 + v1 → (GNorm a b x y).Adj (pt 3 d1) (pt 0 d2) := by
    intro d1 d2 hd; subst hd
    simpa [pt, add_assoc, add_comm, add_left_comm] using adj_shift hc1_3 d1
  have st_end2 : ∀ d1 d2, d2 = d1 + v2 → (GNorm a b x y).Adj (pt 10 d1) (pt 7 d2) := by
    intro d1 d2 hd; subst hd
    simpa [pt, add_assoc, add_comm, add_left_comm] using adj_shift hc2_3 d1
  by_cases hsum : v1 + v2 = 0
  · let idx : Fin 16 → Fin 11 := ![0, 1, 2, 3, 0, 4, 5, 6, 7, 8, 9, 10, 7, 6, 5, 4]
    let off : Fin 16 → V := ![0, 0, 0, 0, v1, v1, v1, v1, v1, v1, v1, v1, 0, 0, 0, 0]
    let f : Fin 16 → Bool × B × V := fun i => pt (idx i) (off i)
    apply hasPow2_of_16 (walk_to_cycle (by decide) f ?_ ?_)
    · refine indexed_walk_inj u hu g idx off [(0, 4), (5, 15), (6, 14), (7, 13), (8, 12)] (by decide) ?_
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp [off]
      · exact hv1.symm
      · exact hv1
      · exact hv1
      · exact hv1
      · exact hv1
    · intro i; fin_cases i <;> dsimp [f, idx, off]
      · exact st hc1_0 rfl
      · exact st hc1_1 rfl
      · exact st hc1_2 rfl
      · exact st_end1 0 v1 (by abel)
      · exact st hb_0 rfl
      · exact st hb_1 rfl
      · exact st hb_2 rfl
      · exact st hb_3 rfl
      · exact st hc2_0 rfl
      · exact st hc2_1 rfl
      · exact st hc2_2 rfl
      · exact st_end2 v1 0 (by linear_combination (norm := abel) -hsum)
      · exact (st hb_3 rfl).symm
      · exact (st hb_2 rfl).symm
      · exact (st hb_1 rfl).symm
      · exact (st hb_0 rfl).symm
  · by_cases hdiff : v1 - v2 = 0
    · let idx : Fin 16 → Fin 11 := ![0, 1, 2, 3, 0, 4, 5, 6, 7, 10, 9, 8, 7, 6, 5, 4]
      let off : Fin 16 → V := ![0, 0, 0, 0, v1, v1, v1, v1, v1, 0, 0, 0, 0, 0, 0, 0]
      let f : Fin 16 → Bool × B × V := fun i => pt (idx i) (off i)
      apply hasPow2_of_16 (walk_to_cycle (by decide) f ?_ ?_)
      · refine indexed_walk_inj u hu g idx off [(0, 4), (5, 15), (6, 14), (7, 13), (8, 12)] (by decide) ?_
        intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp [off]
        · exact hv1.symm
        · exact hv1
        · exact hv1
        · exact hv1
        · exact hv1
      · intro i; fin_cases i <;> dsimp [f, idx, off]
        · exact st hc1_0 rfl
        · exact st hc1_1 rfl
        · exact st hc1_2 rfl
        · exact st_end1 0 v1 (by abel)
        · exact st hb_0 rfl
        · exact st hb_1 rfl
        · exact st hb_2 rfl
        · exact st hb_3 rfl
        · exact (st_end2 0 v1 (by linear_combination (norm := abel) hdiff)).symm
        · exact (st hc2_2 rfl).symm
        · exact (st hc2_1 rfl).symm
        · exact (st hc2_0 rfl).symm
        · exact (st hb_3 rfl).symm
        · exact (st hb_2 rfl).symm
        · exact (st hb_1 rfl).symm
        · exact (st hb_0 rfl).symm
    · let idx : Fin 32 → Fin 11 := ![
        0, 1, 2, 3, 0, 4, 5, 6, 7, 8, 9, 10, 7, 6, 5, 4,
        0, 3, 2, 1, 0, 4, 5, 6, 7, 10, 9, 8, 7, 6, 5, 4]
      let off : Fin 32 → V := ![
        0, 0, 0, 0, v1, v1, v1, v1, v1, v1, v1, v1, v1 + v2, v1 + v2, v1 + v2, v1 + v2,
        v1 + v2, v2, v2, v2, v2, v2, v2, v2, v2, 0, 0, 0, 0, 0, 0, 0]
      let f : Fin 32 → Bool × B × V := fun i => pt (idx i) (off i)
      apply hasPow2_of_32 (walk_to_cycle (by decide) f ?_ ?_)
      · refine indexed_walk_inj u hu g idx off
          [(0, 4), (0, 16), (0, 20), (4, 16), (4, 20), (16, 20),
           (1, 19), (2, 18), (3, 17),
           (5, 15), (5, 21), (5, 31), (15, 21), (15, 31), (21, 31),
           (6, 14), (6, 22), (6, 30), (14, 22), (14, 30), (22, 30),
           (7, 13), (7, 23), (7, 29), (13, 23), (13, 29), (23, 29),
           (8, 12), (8, 24), (8, 28), (12, 24), (12, 28), (24, 28),
           (9, 27), (10, 26), (11, 25)] (by decide) ?_
        intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp [off] <;>
          intro e <;> first
            | (solve | apply hv1; linear_combination (norm := abel) e)
            | (solve | apply hv1; linear_combination (norm := abel) -e)
            | (solve | apply hv2; linear_combination (norm := abel) e)
            | (solve | apply hv2; linear_combination (norm := abel) -e)
            | (solve | apply hsum; linear_combination (norm := abel) e)
            | (solve | apply hsum; linear_combination (norm := abel) -e)
            | (solve | apply hdiff; linear_combination (norm := abel) e)
      · intro i; fin_cases i <;> dsimp [f, idx, off]
        · exact st hc1_0 rfl
        · exact st hc1_1 rfl
        · exact st hc1_2 rfl
        · exact st_end1 0 v1 (by abel)
        · exact st hb_0 rfl
        · exact st hb_1 rfl
        · exact st hb_2 rfl
        · exact st hb_3 rfl
        · exact st hc2_0 rfl
        · exact st hc2_1 rfl
        · exact st hc2_2 rfl
        · exact st_end2 v1 (v1 + v2) (by abel)
        · exact (st hb_3 rfl).symm
        · exact (st hb_2 rfl).symm
        · exact (st hb_1 rfl).symm
        · exact (st hb_0 rfl).symm
        · exact (st_end1 v2 (v1 + v2) (by abel)).symm
        · exact (st hc1_2 rfl).symm
        · exact (st hc1_1 rfl).symm
        · exact (st hc1_0 rfl).symm
        · exact st hb_0 rfl
        · exact st hb_1 rfl
        · exact st hb_2 rfl
        · exact st hb_3 rfl
        · exact (st_end2 0 v2 (by abel)).symm
        · exact (st hc2_2 rfl).symm
        · exact (st hc2_1 rfl).symm
        · exact (st hc2_0 rfl).symm
        · exact (st hb_3 rfl).symm
        · exact (st hb_2 rfl).symm
        · exact (st hb_1 rfl).symm
        · exact (st hb_0 rfl).symm

/-- Theta `(2, 2, 4)`: 3 internally disjoint paths from `u 0` to `u 1` of lengths 2, 2, 4. -/
lemma theta_2_2_4
    (u : Fin 7 → Bool × B) (hu : Function.Injective u)
    (g : Fin 7 → V) (vP vQ vR : V)
    (hPQ : vP ≠ vQ) (hQR : vQ ≠ vR) (hRP : vR ≠ vP)
    (hP0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 2 |>.1, u 2 |>.2, g 2))
    (hP1 : (GNorm a b x y).Adj (u 2 |>.1, u 2 |>.2, g 2) (u 1 |>.1, u 1 |>.2, g 0 + vP))
    (hQ0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 3 |>.1, u 3 |>.2, g 3))
    (hQ1 : (GNorm a b x y).Adj (u 3 |>.1, u 3 |>.2, g 3) (u 1 |>.1, u 1 |>.2, g 0 + vQ))
    (hR0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 4 |>.1, u 4 |>.2, g 4))
    (hR1 : (GNorm a b x y).Adj (u 4 |>.1, u 4 |>.2, g 4) (u 5 |>.1, u 5 |>.2, g 5))
    (hR2 : (GNorm a b x y).Adj (u 5 |>.1, u 5 |>.2, g 5) (u 6 |>.1, u 6 |>.2, g 6))
    (hR3 : (GNorm a b x y).Adj (u 6 |>.1, u 6 |>.2, g 6) (u 1 |>.1, u 1 |>.2, g 0 + vR)) :
    HasPow2 (GNorm a b x y) := by
  let g' : Fin 7 → V := fun k => if k = 1 then g 0 else g k
  let idx : Fin 16 → Fin 7 := ![0, 2, 1, 6, 5, 4, 0, 3, 1, 2, 0, 4, 5, 6, 1, 3]
  let off : Fin 16 → V := ![
    0, 0, vP, vP - vR, vP - vR, vP - vR, vP - vR, vP - vR,
    vP - vR + vQ, vQ - vR, vQ - vR, vQ - vR, vQ - vR, vQ - vR, vQ, 0]
  let f : Fin 16 → Bool × B × V := fun i => ((u (idx i)).1, (u (idx i)).2, g' (idx i) + off i)
  apply hasPow2_of_16 (walk_to_cycle (by decide) f ?_ ?_)
  · refine indexed_walk_inj u hu g' idx off
      [(0, 6), (0, 10), (6, 10), (1, 9), (2, 8), (2, 14), (8, 14),
       (3, 13), (4, 12), (5, 11), (7, 15)] (by decide) ?_
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp [off] <;> intro e <;> first
        | (solve | apply hPQ; linear_combination (norm := abel) e)
        | (solve | apply hPQ; linear_combination (norm := abel) -e)
        | (solve | apply hQR; linear_combination (norm := abel) e)
        | (solve | apply hQR; linear_combination (norm := abel) -e)
        | (solve | apply hRP; linear_combination (norm := abel) e)
        | (solve | apply hRP; linear_combination (norm := abel) -e)
  · intro i; fin_cases i <;> dsimp [f, g', idx, off]
    · simpa using adj_shift hP0 0
    · simpa using adj_shift hP1 0
    · have hv : g 0 + vR + (vP - vR) = g 0 + vP := by abel
      simpa [hv] using (adj_shift hR3 (vP - vR)).symm
    · exact (adj_shift hR2 (vP - vR)).symm
    · exact (adj_shift hR1 (vP - vR)).symm
    · exact (adj_shift hR0 (vP - vR)).symm
    · exact adj_shift hQ0 (vP - vR)
    · have hv : g 0 + vQ + (vP - vR) = g 0 + (vP - vR + vQ) := by abel
      simpa [hv] using adj_shift hQ1 (vP - vR)
    · have hv : g 0 + vP + (vQ - vR) = g 0 + (vP - vR + vQ) := by abel
      simpa [hv] using (adj_shift hP1 (vQ - vR)).symm
    · exact (adj_shift hP0 (vQ - vR)).symm
    · exact adj_shift hR0 (vQ - vR)
    · exact adj_shift hR1 (vQ - vR)
    · exact adj_shift hR2 (vQ - vR)
    · have hv : g 0 + vR + (vQ - vR) = g 0 + vQ := by abel
      simpa [hv] using adj_shift hR3 (vQ - vR)
    · simpa using (adj_shift hQ1 0).symm
    · simpa using (adj_shift hQ0 0).symm

/-- Theta `(2, 10, 4)`: 3 internally disjoint paths from `u 0` to `u 1` of lengths 2, 10, 4. -/
lemma theta_2_10_4
    (u : Fin 15 → Bool × B) (hu : Function.Injective u)
    (g : Fin 15 → V) (vP vQ vR : V)
    (hPQ : vP ≠ vQ) (hQR : vQ ≠ vR) (hRP : vR ≠ vP)
    (hP0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 2 |>.1, u 2 |>.2, g 2))
    (hP1 : (GNorm a b x y).Adj (u 2 |>.1, u 2 |>.2, g 2) (u 1 |>.1, u 1 |>.2, g 0 + vP))
    (hR0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 3 |>.1, u 3 |>.2, g 3))
    (hR1 : (GNorm a b x y).Adj (u 3 |>.1, u 3 |>.2, g 3) (u 4 |>.1, u 4 |>.2, g 4))
    (hR2 : (GNorm a b x y).Adj (u 4 |>.1, u 4 |>.2, g 4) (u 5 |>.1, u 5 |>.2, g 5))
    (hR3 : (GNorm a b x y).Adj (u 5 |>.1, u 5 |>.2, g 5) (u 1 |>.1, u 1 |>.2, g 0 + vR))
    (hQ0 : (GNorm a b x y).Adj (u 0 |>.1, u 0 |>.2, g 0) (u 6 |>.1, u 6 |>.2, g 6))
    (hQ1 : (GNorm a b x y).Adj (u 6 |>.1, u 6 |>.2, g 6) (u 7 |>.1, u 7 |>.2, g 7))
    (hQ2 : (GNorm a b x y).Adj (u 7 |>.1, u 7 |>.2, g 7) (u 8 |>.1, u 8 |>.2, g 8))
    (hQ3 : (GNorm a b x y).Adj (u 8 |>.1, u 8 |>.2, g 8) (u 9 |>.1, u 9 |>.2, g 9))
    (hQ4 : (GNorm a b x y).Adj (u 9 |>.1, u 9 |>.2, g 9) (u 10 |>.1, u 10 |>.2, g 10))
    (hQ5 : (GNorm a b x y).Adj (u 10 |>.1, u 10 |>.2, g 10) (u 11 |>.1, u 11 |>.2, g 11))
    (hQ6 : (GNorm a b x y).Adj (u 11 |>.1, u 11 |>.2, g 11) (u 12 |>.1, u 12 |>.2, g 12))
    (hQ7 : (GNorm a b x y).Adj (u 12 |>.1, u 12 |>.2, g 12) (u 13 |>.1, u 13 |>.2, g 13))
    (hQ8 : (GNorm a b x y).Adj (u 13 |>.1, u 13 |>.2, g 13) (u 14 |>.1, u 14 |>.2, g 14))
    (hQ9 : (GNorm a b x y).Adj (u 14 |>.1, u 14 |>.2, g 14) (u 1 |>.1, u 1 |>.2, g 0 + vQ)) :
    HasPow2 (GNorm a b x y) := by
  let g' : Fin 15 → V := fun k => if k = 1 then g 0 else g k
  let idx : Fin 32 → Fin 15 := ![
    0, 2, 1, 5, 4, 3, 0, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    1, 2, 0, 3, 4, 5, 1, 14, 13, 12, 11, 10, 9, 8, 7, 6]
  let off : Fin 32 → V := ![
    0, 0, vP, vP - vR, vP - vR, vP - vR, vP - vR,
    vP - vR, vP - vR, vP - vR, vP - vR, vP - vR, vP - vR, vP - vR, vP - vR, vP - vR,
    vP - vR + vQ, vQ - vR, vQ - vR, vQ - vR, vQ - vR, vQ - vR,
    vQ, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let f : Fin 32 → Bool × B × V := fun i => ((u (idx i)).1, (u (idx i)).2, g' (idx i) + off i)
  apply hasPow2_of_32 (walk_to_cycle (by decide) f ?_ ?_)
  · refine indexed_walk_inj u hu g' idx off
      [(0, 6), (0, 18), (6, 18), (1, 17), (2, 16), (2, 22), (16, 22),
       (3, 21), (4, 20), (5, 19),
       (7, 31), (8, 30), (9, 29), (10, 28), (11, 27), (12, 26), (13, 25), (14, 24), (15, 23)]
      (by decide) ?_
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp [off] <;> intro e <;> first
        | (solve | apply hPQ; linear_combination (norm := abel) e)
        | (solve | apply hPQ; linear_combination (norm := abel) -e)
        | (solve | apply hQR; linear_combination (norm := abel) e)
        | (solve | apply hQR; linear_combination (norm := abel) -e)
        | (solve | apply hRP; linear_combination (norm := abel) e)
        | (solve | apply hRP; linear_combination (norm := abel) -e)
  · intro i; fin_cases i <;> dsimp [f, g', idx, off]
    · simpa using adj_shift hP0 0
    · simpa using adj_shift hP1 0
    · have hv : g 0 + vR + (vP - vR) = g 0 + vP := by abel
      simpa [hv] using (adj_shift hR3 (vP - vR)).symm
    · exact (adj_shift hR2 (vP - vR)).symm
    · exact (adj_shift hR1 (vP - vR)).symm
    · exact (adj_shift hR0 (vP - vR)).symm
    · exact adj_shift hQ0 (vP - vR)
    · exact adj_shift hQ1 (vP - vR)
    · exact adj_shift hQ2 (vP - vR)
    · exact adj_shift hQ3 (vP - vR)
    · exact adj_shift hQ4 (vP - vR)
    · exact adj_shift hQ5 (vP - vR)
    · exact adj_shift hQ6 (vP - vR)
    · exact adj_shift hQ7 (vP - vR)
    · exact adj_shift hQ8 (vP - vR)
    · have hv : g 0 + vQ + (vP - vR) = g 0 + (vP - vR + vQ) := by abel
      simpa [hv] using adj_shift hQ9 (vP - vR)
    · have hv : g 0 + vP + (vQ - vR) = g 0 + (vP - vR + vQ) := by abel
      simpa [hv] using (adj_shift hP1 (vQ - vR)).symm
    · exact (adj_shift hP0 (vQ - vR)).symm
    · exact adj_shift hR0 (vQ - vR)
    · exact adj_shift hR1 (vQ - vR)
    · exact adj_shift hR2 (vQ - vR)
    · have hv : g 0 + vR + (vQ - vR) = g 0 + vQ := by abel
      simpa [hv] using adj_shift hR3 (vQ - vR)
    · simpa using (adj_shift hQ9 0).symm
    · simpa using (adj_shift hQ8 0).symm
    · simpa using (adj_shift hQ7 0).symm
    · simpa using (adj_shift hQ6 0).symm
    · simpa using (adj_shift hQ5 0).symm
    · simpa using (adj_shift hQ4 0).symm
    · simpa using (adj_shift hQ3 0).symm
    · simpa using (adj_shift hQ2 0).symm
    · simpa using (adj_shift hQ1 0).symm
    · simpa using (adj_shift hQ0 0).symm

end WalkEngines

/- ## Section 2: General Case (No small linear relations in `B`) -/

section GeneralCase
variable {B V : Type*} [AddCommGroup B] [AddCommGroup V]
variable {a b : B} {x y : B → V}

/-- The 18 nonzero base differences `(p, q)` that can appear in the 3 general-case walks
(Barbell, Theta, 4-hex 16-cycle). Avoiding the 4 forbidden `S_3`-orbits means all 18 are nonzero. -/
def GeneralPos (a b : B) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
  a + a ≠ 0 ∧ b + b ≠ 0 ∧ (a - b) + (a - b) ≠ 0 ∧
  3 • a ≠ 0 ∧ 3 • b ≠ 0 ∧ 3 • (a - b) ≠ 0 ∧
  a ≠ 2 • b ∧ b ≠ 2 • a ∧ a + b ≠ 0 ∧
  a ≠ 3 • b ∧ b ≠ 3 • a ∧ a + 2 • b ≠ 0 ∧ 2 • a + b ≠ 0 ∧ 3 • a ≠ 2 • b ∧ 2 • a ≠ 3 • b

lemma generalPos_swap_ab (h : GeneralPos a b) : GeneralPos b a := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  refine ⟨h2, h1, h3.symm, h5, h4, ?_, h8, h7, ?_, h11, h10, ?_, h14, h13, ?_, ?_, h18.symm, h17.symm⟩
  · intro e; exact h6 (by linear_combination (norm := abel) -e)
  · intro e; exact h9 (by simp only [smul_sub] at e ⊢; linear_combination (norm := abel) -e)
  · intro e; exact h12 (by linear_combination (norm := abel) e)
  · intro e; exact h16 (by linear_combination (norm := abel) e)
  · intro e; exact h15 (by linear_combination (norm := abel) e)

lemma generalPos_swap_0a (h : GeneralPos a b) : GeneralPos (-a) (b - a) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; exact h1 (by linear_combination (norm := abel) -e)
  · intro e; exact h3 (by linear_combination (norm := abel) -e)
  · intro e; exact h2 (by linear_combination (norm := abel) -e)
  · intro e; exact h4 (by linear_combination (norm := abel) -e)
  · intro e; exact h6 (by linear_combination (norm := abel) -e)
  · intro e; exact h5 (by linear_combination (norm := abel) -e)
  · intro e; exact h7 (by simp only [smul_neg] at e; linear_combination (norm := abel) -e)
  · intro e; exact h9 (by simp only [smul_sub] at e ⊢; linear_combination (norm := abel) -e)
  · intro e; exact h8 (by simp only [smul_sub, smul_neg] at e; linear_combination (norm := abel) -e)
  · intro e; exact h10 (by simp only [smul_sub] at e; linear_combination (norm := abel) e)
  · intro e; exact h12 (by simp only [smul_neg] at e; linear_combination (norm := abel) e)
  · intro e; exact h11 (by linear_combination (norm := abel) e)
  · intro e; exact h18 (by simp only [smul_sub] at e; linear_combination (norm := abel) e)
  · intro e; exact h16 (by simp only [smul_neg] at e; linear_combination (norm := abel) e)
  · intro e; exact h17 (by simp only [smul_sub] at e; linear_combination (norm := abel) -e)
  · intro e; exact h14 (by simp only [smul_neg] at e; linear_combination (norm := abel) e)
  · intro e; exact h15 (by simp only [smul_sub, smul_neg] at e; linear_combination (norm := abel) -e)
  · intro e; exact h13 (by simp only [smul_sub, smul_neg] at e; linear_combination (norm := abel) e)

/-- Helper: under `GeneralPos a b`, any linear combination `p • a + q • b = 0` with small `p, q`
is impossible. -/
lemma generalPos_lin_ne_zero (h : GeneralPos a b) :
    (a ≠ 0) ∧ (b ≠ 0) ∧ (a - b ≠ 0) ∧
    (2 • a ≠ 0) ∧ (2 • b ≠ 0) ∧ (2 • a - 2 • b ≠ 0) ∧
    (3 • a ≠ 0) ∧ (3 • b ≠ 0) ∧ (3 • a - 3 • b ≠ 0) ∧
    (a - 2 • b ≠ 0) ∧ (2 • a - b ≠ 0) ∧ (a + b ≠ 0) ∧
    (a - 3 • b ≠ 0) ∧ (3 • a - b ≠ 0) ∧ (a + 2 • b ≠ 0) ∧
    (2 • a + b ≠ 0) ∧ (3 • a - 2 • b ≠ 0) ∧ (2 • a - 3 • b ≠ 0) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  refine ⟨h1, h2, sub_ne_zero.mpr h3, ?_, ?_, ?_, h7, h8, ?_,
    sub_ne_zero.mpr h10, sub_ne_zero.mpr h11.symm, h12,
    sub_ne_zero.mpr h13, sub_ne_zero.mpr h14.symm, h15, h16,
    sub_ne_zero.mpr h17, sub_ne_zero.mpr h18⟩
  · intro e; exact h4 (by linear_combination (norm := abel) e)
  · intro e; exact h5 (by linear_combination (norm := abel) e)
  · intro e; exact h6 (by linear_combination (norm := abel) e)
  · intro e; exact h9 (by linear_combination (norm := abel) e)

/-- Fast injectivity helper under `GeneralPos a b`: any of the 36 small nonzero `ℤ`-linear
combinations `p • a + q • b` is nonzero. -/
def gpDiffs : List (ℤ × ℤ) :=
  [(1,0), (-1,0), (0,1), (0,-1), (1,-1), (-1,1),
   (2,0), (-2,0), (0,2), (0,-2), (2,-2), (-2,2),
   (3,0), (-3,0), (0,3), (0,-3), (3,-3), (-3,3),
   (1,-2), (-1,2), (2,-1), (-2,1), (1,1), (-1,-1),
   (1,-3), (-1,3), (3,-1), (-3,1), (1,2), (-1,-2),
   (2,1), (-2,-1), (3,-2), (-3,2), (2,-3), (-2,3)]

lemma generalPos_zsmul_ne (hgp : GeneralPos a b) {p q : ℤ} (hpq : (p, q) ∈ gpDiffs) :
    p • a + q • b ≠ 0 := by
  have hlin := generalPos_lin_ne_zero hgp
  simp only [gpDiffs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpq
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals intro e; simp only [zero_zsmul, one_zsmul, neg_zsmul, add_zero, zero_add] at e
  · exact hlin.1 (by linear_combination (norm := abel) e)
  · exact hlin.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by linear_combination (norm := abel) -e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by linear_combination (norm := abel) e)
  · exact hlin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by linear_combination (norm := abel) -e)

lemma generalPos_coord_inj {m : ℕ} (hgp : GeneralPos a b) (coords : Fin m → Bool × ℤ × ℤ)
    (hdiff : ∀ i j : Fin m, i ≠ j → (coords i).1 = (coords j).1 →
      ((coords i).2.1 - (coords j).2.1, (coords i).2.2 - (coords j).2.2) ∈ gpDiffs) :
    Function.Injective (fun k : Fin m =>
      ((coords k).1, (coords k).2.1 • a + (coords k).2.2 • b)) := by
  intro i j hij
  by_contra hne
  have hs : (coords i).1 = (coords j).1 := congrArg (fun z : Bool × B => z.1) hij
  have hb : (coords i).2.1 • a + (coords i).2.2 • b = (coords j).2.1 • a + (coords j).2.2 • b :=
    congrArg (fun z : Bool × B => z.2) hij
  have hz : ((coords i).2.1 - (coords j).2.1) • a + ((coords i).2.2 - (coords j).2.2) • b = 0 := by
    rw [sub_zsmul, sub_zsmul]; linear_combination (norm := abel) hb
  exact generalPos_zsmul_ne hgp (hdiff i j hne hs) hz

/-- Barbell `(6, 2, 6)` in direction `2a`: if `hexV i ≠ 0` and `hexV (i + 2a) ≠ 0`, then `HasPow2`. -/
lemma general_barbell_2a (hgp : GeneralPos a b) (i : B)
    (h1 : hexV a b x y i ≠ 0) (h2 : hexV a b x y (i + (a + a)) ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  apply hasPow2_mono (gnorm_translate i)
  let x' := fun j => x (j + i)
  let y' := fun j => y (j + i)
  have h1' : hexV a b x' y' 0 ≠ 0 := by
    simpa [hexV, x', y', add_comm] using h1
  have h2' : hexV a b x' y' (a + a) ≠ 0 := by
    have eq1 : a + a + i = i + (a + a) := add_comm _ _
    have eq2 : a + a + a + i = i + (a + a) + a := by abel
    have eq3 : a + a + b + i = i + (a + a) + b := by abel
    simpa [hexV, x', y', eq1, eq2, eq3] using h2
  let coords : Fin 13 → Bool × ℤ × ℤ := ![
    (false, 1, 0), (true, 1, 1), (false, 0, 1), (true, 0, 1), (false, 0, 0), (true, 1, 0),
    (true, 2, 0),
    (false, 2, 0), (true, 3, 0), (false, 3, 0), (true, 3, 1), (false, 2, 1), (true, 2, 1)]
  let u : Fin 13 → Bool × B := fun k => ((coords k).1, (coords k).2.1 • a + (coords k).2.2 • b)
  have hu : Function.Injective u := generalPos_coord_inj hgp coords (by decide)
  let g : Fin 13 → V := ![
    0,
    y' a,
    y' a - x' b,
    y' a - x' b,
    y' a - x' b - y' 0,
    y' a - x' b - y' 0 + x' 0,
    x' a,
    x' a,
    x' a + x' (2 • a),
    x' a + x' (2 • a),
    x' a + x' (2 • a) + y' (3 • a),
    x' a + x' (2 • a) + y' (3 • a) - x' (2 • a + b),
    x' a + x' (2 • a) + y' (3 • a) - x' (2 • a + b)]
  have h2z : (2 : ℤ) • a = 2 • a := by abel
  have h3z : (3 : ℤ) • a = 3 • a := by abel
  have hba : b + a = a + b := add_comm _ _
  refine barbell_6_2_6 u hu g (hexV a b x' y' 0) (hexV a b x' y' (a + a)) h1' h2'
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    simpa [zero_add] using eb (a := a) (b := b) (x := x') (y := y') a 0
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    rw [← hba]; simpa [sub_add_cancel] using ea' (a := a) (b := b) (x := x') (y := y') b (y' a - x' b)
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    exact e0 b (y' a - x' b)
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    simpa [zero_add, sub_add_cancel] using eb' (a := a) (b := b) (x := x') (y := y') 0 (y' a - x' b - y' 0)
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    simpa [zero_add] using ea (a := a) (b := b) (x := x') (y := y') 0 (y' a - x' b - y' 0)
  · have hv : y' a - x' b - y' 0 + x' 0 = hexV a b x' y' 0 := by simp [hexV]; abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    rw [hv]; exact e0' (a := a) (b := b) (x := x') (y := y') a (hexV a b x' y' 0)
  · have hb2 : a + a = 2 • a := by abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    rw [← hb2]; simpa [zero_add] using ea (a := a) (b := b) (x := x') (y := y') a 0
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    exact e0' (2 • a) (x' a)
  · have h3 : 2 • a + a = 3 • a := by abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    rw [← h3]; exact ea (2 • a) (x' a)
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    exact e0' (3 • a) (x' a + x' (2 • a))
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    exact eb (3 • a) (x' a + x' (2 • a))
  · have h3b : 2 • a + b + a = 3 • a + b := by abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    rw [← h3b]
    have h := ea' (a := a) (b := b) (x := x') (y := y') (2 • a + b) (x' a + x' (2 • a) + y' (3 • a) - x' (2 • a + b))
    rwa [sub_add_cancel] at h
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    exact e0 (2 • a + b) (x' a + x' (2 • a) + y' (3 • a) - x' (2 • a + b))
  · have h2a : a + a = 2 • a := by abel
    have h3a : a + a + a = 3 • a := by abel
    have hv : x' a + hexV a b x' y' (a + a) + y' (2 • a) =
        x' a + x' (2 • a) + y' (3 • a) - x' (2 • a + b) := by
      simp [hexV, h2a, h3a]; abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2z, h3z]
    rw [← hv]; exact eb' (2 • a) (x' a + hexV a b x' y' (a + a))

/-- Barbell in direction `2b` (by `swap_ab`). -/
lemma general_barbell_2b (hgp : GeneralPos a b) (i : B)
    (h1 : hexV a b x y i ≠ 0) (h2 : hexV a b x y (i + (b + b)) ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  apply hasPow2_mono gnorm_swap_ab
  apply general_barbell_2a (generalPos_swap_ab hgp) i
  · intro e; exact h1 (by dsimp [hexV] at e ⊢; linear_combination (norm := abel) -e)
  · intro e; exact h2 (by dsimp [hexV] at e ⊢; linear_combination (norm := abel) -e)

/-- Barbell in direction `2a - 2b` (by `swap_0a`). -/
lemma general_barbell_2ab (hgp : GeneralPos a b) (i : B)
    (h1 : hexV a b x y i ≠ 0) (h2 : hexV a b x y (i + (a + a) - (b + b)) ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  apply hasPow2_mono gnorm_swap_0a
  -- Under swap_0a, a' = -a, b' = b - a, so 2b' = 2b - 2a = -(2a - 2b)!
  -- Check hexV (-a) (b - a) x' y' j = - hexV a b x y (j - a)!
  have hhex : ∀ j : B,
      hexV (-a) (b - a) (fun k => -x (k - a)) (fun k => y k - x (k + b - a)) j =
        - hexV a b x y (j - a) := by
    intro j
    dsimp [hexV]
    have e1 : j + -a = j - a := by abel
    have e2 : j + (b - a) - a = j - a + b - a := by abel
    have e3 : j + -a + b - a = j - a + b - a := by abel
    have e4 : j - a + a = j := by abel
    have e5 : j + (b - a) - a = j - a + b - a := by abel
    rw [e1, e4]
    have e6 : j + (b - a) = j - a + b := by abel
    rw [e6]
    abel
  apply general_barbell_2b (generalPos_swap_0a hgp) (i + (a + a) - (b + b) + a)
  · rw [hhex]; simp only [add_sub_cancel_right, neg_ne_zero]; exact h2
  · rw [hhex]
    have e : i + (a + a) - (b + b) + a + (b - a + (b - a)) - a = i := by abel
    rw [e, neg_ne_zero]; exact h1

/-- Theta `(2, 10, 4)` on star `[H(0), H(a), H(b)]` and `H(a + b)` under `GeneralPos a b`. -/
lemma general_theta (hgp : GeneralPos a b)
    (ha0 : hexV a b x y a = 0) (hb0 : hexV a b x y b = 0)
    (h0 : hexV a b x y 0 ≠ 0) (hab : hexV a b x y (a + b) ≠ 0)
    (hsum : hexV a b x y 0 + hexV a b x y (a + b) ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  let coords : Fin 15 → Bool × ℤ × ℤ := ![
    (true, 2, 1), (true, 1, 2),
    (false, 1, 1),
    (false, 2, 1), (true, 2, 2), (false, 1, 2),
    (false, 2, 0), (true, 2, 0), (false, 1, 0), (true, 1, 0),
    (false, 0, 0), (true, 0, 1), (false, 0, 1), (true, 0, 2), (false, 0, 2)]
  let u : Fin 15 → Bool × B := fun k => ((coords k).1, (coords k).2.1 • a + (coords k).2.2 • b)
  have hu : Function.Injective u := generalPos_coord_inj hgp coords (by decide)
  have h2a : (2 : ℤ) • a = 2 • a := by abel
  have h2b : (2 : ℤ) • b = 2 • b := by abel
  let vP : V := -x (a + b) + y (a + b)
  let vR : V := y (2 • a + b) - x (a + 2 • b)
  let vQ : V := -y (2 • a) - x a - x 0 + y 0 + y b + x (2 • b)
  have hvPR : vP - vR = -hexV a b x y (a + b) := by
    have e1 : a + b + a = 2 • a + b := by abel
    have e2 : a + b + b = a + 2 • b := by abel
    dsimp [vP, vR, hexV]; rw [e1, e2]; abel
  have hvPQ : vP - vQ = hexV a b x y 0 + hexV a b x y a + hexV a b x y b := by
    have e1 : a + a = 2 • a := by abel
    have e2 : b + b = 2 • b := by abel
    have e3 : b + a = a + b := by abel
    dsimp [vP, vQ, hexV]; rw [e1, e2, e3]; abel
  have hPQ : vP ≠ vQ := by
    intro e
    have : hexV a b x y 0 = 0 := by
      have := sub_eq_zero.mpr e; rw [hvPQ, ha0, hb0] at this; simpa using this
    exact h0 this
  have hRP : vR ≠ vP := by
    intro e
    have : hexV a b x y (a + b) = 0 := by
      have := sub_eq_zero.mpr e.symm; rw [hvPR] at this; simpa using this
    exact hab this
  have hQR : vQ ≠ vR := by
    intro e
    have h1 : vP - vQ = vP - vR := by rw [e]
    rw [hvPQ, hvPR, ha0, hb0] at h1
    exact hsum (by linear_combination (norm := abel) h1)
  let g : Fin 15 → V := ![
    0, 0,
    -x (a + b),
    0, y (2 • a + b), y (2 • a + b) - x (a + 2 • b),
    -y (2 • a), -y (2 • a), -y (2 • a) - x a, -y (2 • a) - x a,
    -y (2 • a) - x a - x 0, -y (2 • a) - x a - x 0 + y 0,
    -y (2 • a) - x a - x 0 + y 0, -y (2 • a) - x a - x 0 + y 0 + y b,
    -y (2 • a) - x a - x 0 + y 0 + y b]
  refine theta_2_10_4 u hu g vP vQ vR hPQ hQR hRP
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have e1 : a + b + a = 2 • a + b := by abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    rw [← e1]; simpa [neg_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) (a + b) (-x (a + b))
  · have e1 : a + b + b = a + 2 • b := by abel
    dsimp [u, coords, g, vP]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    rw [← e1]; exact eb (a + b) (-x (a + b))
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    exact e0' (2 • a + b) 0
  · have e1 : 2 • a + b + b = 2 • a + 2 • b := by abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    rw [← e1]; simpa [zero_add] using eb (a := a) (b := b) (x := x) (y := y) (2 • a + b) 0
  · have e1 : a + 2 • b + a = 2 • a + 2 • b := by abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    rw [← e1]
    have h := ea' (a := a) (b := b) (x := x) (y := y) (a + 2 • b) (y (2 • a + b) - x (a + 2 • b))
    rwa [sub_add_cancel] at h
  · dsimp [u, coords, g, vR]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    exact e0 (a + 2 • b) (y (2 • a + b) - x (a + 2 • b))
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    have h := eb' (a := a) (b := b) (x := x) (y := y) (2 • a) (-y (2 • a))
    rwa [neg_add_cancel] at h
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    exact e0 (2 • a) (-y (2 • a))
  · have e1 : a + a = 2 • a := by abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    have h := ea' (a := a) (b := b) (x := x) (y := y) a (-y (2 • a) - x a)
    rwa [e1, sub_add_cancel] at h
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    exact e0 a (-y (2 • a) - x a)
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    simpa [zero_add, sub_add_cancel] using
      ea' (a := a) (b := b) (x := x) (y := y) 0 (-y (2 • a) - x a - x 0)
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    simpa [zero_add] using eb (a := a) (b := b) (x := x) (y := y) 0 (-y (2 • a) - x a - x 0)
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    exact e0' b (-y (2 • a) - x a - x 0 + y 0)
  · have e1 : b + b = 2 • b := by abel
    dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    rw [← e1]; exact eb b (-y (2 • a) - x a - x 0 + y 0)
  · dsimp [u, coords, g]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    exact e0' (2 • b) (-y (2 • a) - x a - x 0 + y 0 + y b)
  · have e1 : 2 • b + a = a + 2 • b := by abel
    dsimp [u, coords, g, vQ]
    simp only [zero_zsmul, one_zsmul, zero_add, add_zero, h2a, h2b]
    rw [← e1]; simpa [add_assoc] using ea (a := a) (b := b) (x := x) (y := y) (2 • b) (-y (2 • a) - x a - x 0 + y 0 + y b)

/-- 4-hexagon 16-cycle on `[H(0), H(a - b), H(a), H(a + b)]`: if the sum of the 4 hexagon
voltages is `0`, then `cycleGraph 16 ⊑ G`. -/
lemma general_cluster_16 (hgp : GeneralPos a b)
    (hsum : hexV a b x y 0 + hexV a b x y (a - b) + hexV a b x y a + hexV a b x y (a + b) = 0) :
    HasPow2 (GNorm a b x y) := by
  let coords : Fin 16 → Bool × ℤ × ℤ := ![
    (false, 0, 0), (true, 1, 0), (false, 1, -1), (true, 2, -1),
    (false, 2, -1), (true, 2, 0), (false, 2, 0), (true, 2, 1),
    (false, 2, 1), (true, 2, 2), (false, 1, 2), (true, 1, 2),
    (false, 1, 1), (true, 1, 1), (false, 0, 1), (true, 0, 1)]
  let u : Fin 16 → Bool × B := fun k => ((coords k).1, (coords k).2.1 • a + (coords k).2.2 • b)
  have hu : Function.Injective u := generalPos_coord_inj hgp coords (by decide)
  have h2a : (2 : ℤ) • a = 2 • a := by abel
  have h2b : (2 : ℤ) • b = 2 • b := by abel
  have h1m1 : (1 : ℤ) • a + (-1 : ℤ) • b = a - b := by abel
  have h2m1 : (2 : ℤ) • a + (-1 : ℤ) • b = 2 • a - b := by abel
  let g : Fin 16 → V := ![
    0,
    x 0,
    x 0 - y (a - b),
    x 0 - y (a - b) + x (a - b),
    x 0 - y (a - b) + x (a - b),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b) - x (a + 2 • b),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b) - x (a + 2 • b),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b) - x (a + 2 • b) - y (a + b),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b) - x (a + 2 • b) - y (a + b),
    x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b) - x (a + 2 • b) - y (a + b) - x b,
    x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b) - x (a + 2 • b) - y (a + b) - x b]
  let f : Fin 16 → Bool × B × V := fun k => ((u k).1, (u k).2, g k)
  apply hasPow2_of_16 (walk_to_cycle (by decide) f ?_ ?_)
  · intro p q hpq
    exact hu (Prod.ext (congrArg (fun z : Bool × B × V => z.1) hpq) (congrArg (fun z : Bool × B × V => z.2.1) hpq))
  · intro k
    fin_cases k <;> dsimp [f, u, coords, g] <;>
      simp only [zero_zsmul, one_zsmul, neg_zsmul, zero_add, add_zero, h2a, h2b, h1m1, h2m1, ← sub_eq_add_neg]
    · simpa using ea (a := a) (b := b) (x := x) (y := y) 0 0
    · have e1 : a - b + b = a := by abel
      rw [← e1]; simpa [sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) (a - b) (x 0 - y (a - b))
    · have e1 : a - b + a = 2 • a - b := by abel
      rw [← e1]; exact ea (a - b) (x 0 - y (a - b))
    · exact e0' (2 • a - b) _
    · have e1 : 2 • a - b + b = 2 • a := by abel
      have h := eb (a := a) (b := b) (x := x) (y := y) (2 • a - b) (x 0 - y (a - b) + x (a - b))
      rwa [e1] at h
    · exact e0' (2 • a) _
    · exact eb (2 • a) _
    · exact e0' (2 • a + b) _
    · have e1 : 2 • a + b + b = 2 • a + 2 • b := by abel
      rw [← e1]; exact eb (2 • a + b) _
    · have e1 : a + 2 • b + a = 2 • a + 2 • b := by abel
      have h := ea' (a := a) (b := b) (x := x) (y := y) (a + 2 • b) (x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b) - x (a + 2 • b))
      rwa [e1, sub_add_cancel] at h
    · exact e0 (a + 2 • b) _
    · have e1 : a + b + b = a + 2 • b := by abel
      have h := eb' (a := a) (b := b) (x := x) (y := y) (a + b) (x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b) - x (a + 2 • b) - y (a + b))
      rwa [e1, sub_add_cancel] at h
    · exact e0 (a + b) _
    · have e1 : b + a = a + b := by abel
      have h := ea' (a := a) (b := b) (x := x) (y := y) b (x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) + y (2 • a + b) - x (a + 2 • b) - y (a + b) - x b)
      rwa [e1, sub_add_cancel] at h
    · exact e0 b _
    · have hv : 0 + y 0 = x 0 - y (a - b) + x (a - b) + y (2 • a - b) + y (2 • a) +
          y (2 • a + b) - x (a + 2 • b) - y (a + b) - x b := by
        have e1 : a - b + a = 2 • a - b := by abel
        have e2 : a - b + b = a := by abel
        have e3 : a + a = 2 • a := by abel
        have e4 : a + b + a = 2 • a + b := by abel
        have e5 : a + b + b = a + 2 • b := by abel
        dsimp [hexV] at hsum
        rw [e1, e2, e3, e4, e5] at hsum
        linear_combination (norm := abel) -hsum
      rw [← hv]; simpa [zero_add] using eb' (a := a) (b := b) (x := x) (y := y) 0 0

/-- Complete proof of the General Case (`GeneralPos a b`, `[Finite B]`). -/
theorem general_case [Finite B] (hgp : GeneralPos a b) : HasPow2 (GNorm a b x y) := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  by_contra hno
  let S : Finset B := Finset.univ.filter fun i => hexV a b x y i ≠ 0
  let ind (i : B) : ℕ := if i ∈ S then 1 else 0
  have hsum_ind : ∑ i : B, ind i = S.card := by simp [ind]
  have hsum_shift : ∀ d : B, ∑ i : B, ind (i + d) = S.card := fun d =>
    (Equiv.sum_comp (Equiv.addRight d) ind).trans hsum_ind
  -- Lower bound: |B| ≤ 3 * |S| from LocalCommutation
  have hlow_pt : ∀ i : B, 2 ≤ 2 * ind i + ind (i + a) + ind (i - a) + ind (i + b) + ind (i - b) := by
    intro i
    by_cases hi : i ∈ S
    · have : ind i = 1 := if_pos hi; omega
    · have hi0 : hexV a b x y i = 0 := by simpa [S] using hi
      have hloc := local_comm_bound hgp.1 hgp.2.1 hgp.2.2.1 hno i hi0
      have h0 : ind i = 0 := if_neg hi
      simp only [ind, S, h0, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, ite_not] at hloc ⊢
      omega
  have hlow : 2 * Fintype.card B ≤ 6 * S.card := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlow_pt i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, hsum_ind, hsum_shift, show ∀ i : B, i - a = i + (-a) from fun _ => sub_eq_add_neg _ _,
      show ∀ i : B, i - b = i + (-b) from fun _ => sub_eq_add_neg _ _] at h
    omega
  -- Upper bound: 3 * |S| ≤ |B| from Barbell triangle {i, i+2a, i+2b}
  have hbar_2a : ∀ i : B, i ∈ S → i + (a + a) ∉ S := fun i hi h2 =>
    hno (general_barbell_2a hgp i (by simpa [S] using hi) (by simpa [S] using h2))
  have hbar_2b : ∀ i : B, i ∈ S → i + (b + b) ∉ S := fun i hi h2 =>
    hno (general_barbell_2b hgp i (by simpa [S] using hi) (by simpa [S] using h2))
  have hbar_2ab : ∀ i : B, i ∈ S → i + (a + a) - (b + b) ∉ S := fun i hi h2 =>
    hno (general_barbell_2ab hgp i (by simpa [S] using hi) (by simpa [S] using h2))
  have hup_pt : ∀ i : B, ind i + ind (i + (a + a)) + ind (i + (b + b)) ≤ 1 := by
    intro i
    by_cases h1 : i ∈ S
    · have h2 : i + (a + a) ∉ S := hbar_2a i h1
      have h3 : i + (b + b) ∉ S := hbar_2b i h1
      simp [ind, h1, h2, h3]
    · by_cases h2 : i + (a + a) ∈ S
      · by_cases h3 : i + (b + b) ∈ S
        · exfalso
          have hbad := hbar_2ab (i + (b + b)) h3
          have heq : i + (b + b) + (a + a) - (b + b) = i + (a + a) := by abel
          rw [heq] at hbad; exact hbad h2
        · simp [ind, h1, h2, h3]
      · by_cases h3 : i + (b + b) ∈ S <;> simp [ind, h1, h2, h3]
  have hup : 3 * S.card ≤ Fintype.card B := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hup_pt i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      hsum_ind, hsum_shift] at h
    omega
  -- Exact equality 3 * |S| = |B| forces EVERY i ∈ S to have all 4 neighbors ∉ S!
  have heq_sum : ∑ i : B, (2 * ind i + ind (i + a) + ind (i - a) + ind (i + b) + ind (i - b)) =
      ∑ _i : B, (2 : ℕ) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, hsum_ind, hsum_shift, show ∀ i : B, i - a = i + (-a) from fun _ => sub_eq_add_neg _ _,
      show ∀ i : B, i - b = i + (-b) from fun _ => sub_eq_add_neg _ _]
    omega
  have heq_pt : ∀ i : B, 2 * ind i + ind (i + a) + ind (i - a) + ind (i + b) + ind (i - b) = 2 := by
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hlow_pt i)).mp heq_sum.symm
    intro i; exact (this i (Finset.mem_univ i)).symm
  -- Pick some i0 ∈ S (since Fintype.card B ≥ 1, S.card ≥ 1)
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hE
    have : Fintype.card B = 0 := by
      have hc : S.card = 0 := by simp [hE]
      omega
    exact Fintype.card_ne_zero this
  obtain ⟨i0, hi0⟩ := hSne
  -- Translate by i0 so 0 ∈ S!
  have hno' : ¬ HasPow2 (GNorm a b (fun j => x (j + i0)) (fun j => y (j + i0))) :=
    fun h => hno (hasPow2_mono (gnorm_translate i0) h)
  -- For any j ∈ S, all 4 neighbors j ± a, j ± b are ∉ S:
  have hnb : ∀ j ∈ S, j + a ∉ S ∧ j - a ∉ S ∧ j + b ∉ S ∧ j - b ∉ S := by
    intro j hj
    have h2 := heq_pt j
    have hj1 : ind j = 1 := if_pos hj
    rw [hj1] at h2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hmem <;> (have : ind _ = 1 := if_pos hmem; omega)
  have h0_nb := hnb i0 hi0
  -- Look at i0 + a ∉ S: its 4 neighbors are i0 (∈ S), i0 + 2a (∉ S), i0 + a + b, i0 + a - b!
  have hia_eq := heq_pt (i0 + a)
  have hia0 : ind (i0 + a) = 0 := if_neg h0_nb.1
  have h2a0 : ind (i0 + a + a) = 0 := if_neg (by simpa [add_assoc] using hbar_2a i0 hi0)
  have hi0_1 : ind (i0 + a - a) = 1 := if_pos (by simpa using hi0)
  rw [hia0, h2a0, hi0_1] at hia_eq
  -- So either i0 + a + b ∈ S or i0 + a - b ∈ S!
  by_cases hab_mem : i0 + a + b ∈ S
  · -- Case 1: i0 + a + b ∈ S!
    have ha_zero : hexV a b (fun j => x (j + i0)) (fun j => y (j + i0)) a = 0 := by
      have : hexV a b x y (i0 + a) = 0 := by simpa [S] using h0_nb.1
      simpa [hexV, add_assoc, add_comm, add_left_comm] using this
    have hb_zero : hexV a b (fun j => x (j + i0)) (fun j => y (j + i0)) b = 0 := by
      have : hexV a b x y (i0 + b) = 0 := by simpa [S] using h0_nb.2.2.1
      simpa [hexV, add_assoc, add_comm, add_left_comm] using this
    have h0_nz : hexV a b (fun j => x (j + i0)) (fun j => y (j + i0)) 0 ≠ 0 := by
      have : hexV a b x y i0 ≠ 0 := by simpa [S] using hi0
      simpa [hexV, add_assoc, add_comm, add_left_comm] using this
    have hab_nz : hexV a b (fun j => x (j + i0)) (fun j => y (j + i0)) (a + b) ≠ 0 := by
      have : hexV a b x y (i0 + a + b) ≠ 0 := by simpa [S] using hab_mem
      simpa [hexV, add_assoc, add_comm, add_left_comm] using this
    have hsum0 : hexV a b (fun j => x (j + i0)) (fun j => y (j + i0)) 0 +
        hexV a b (fun j => x (j + i0)) (fun j => y (j + i0)) (a + b) = 0 := by
      by_contra hne
      exact hno' (general_theta hgp ha_zero hb_zero h0_nz hab_nz hne)
    -- Also (a - b) = (a + b) - 2b ∉ S (barbell of a + b ∈ S)!
    have hamb_not : i0 + a - b ∉ S := by
      intro hmem
      have hbad := hbar_2b (i0 + a - b) hmem
      have heq : i0 + a - b + (b + b) = i0 + a + b := by abel
      rw [heq] at hbad; exact hbad hab_mem
    have hamb_zero : hexV a b (fun j => x (j + i0)) (fun j => y (j + i0)) (a - b) = 0 := by
      have : hexV a b x y (i0 + a - b) = 0 := by simpa [S] using hamb_not
      have e1 : a - b + i0 = i0 + a - b := by abel
      have e2 : a - b + a + i0 = i0 + a - b + a := by abel
      have e3 : a - b + b + i0 = i0 + a - b + b := by abel
      dsimp [hexV] at this ⊢; rw [e1, e2, e3]; exact this
    exact hno' (general_cluster_16 hgp (by rw [ha_zero, hamb_zero]; linear_combination (norm := abel) hsum0))
  · -- Case 2: i0 + a - b ∈ S!
    have hab_0 : ind (i0 + a + b) = 0 := if_neg hab_mem
    rw [hab_0] at hia_eq
    have hamb_mem : i0 + a - b ∈ S := by
      by_contra hnot
      have : ind (i0 + a - b) = 0 := if_neg hnot
      omega
    -- Now look at i0 + b ∉ S: its 4 neighbors are i0 (∈ S), i0+2b (∉ S), i0+a+b (∉ S), i0-a+b (∉ S)!
    have hib_eq := heq_pt (i0 + b)
    have hib0 : ind (i0 + b) = 0 := if_neg h0_nb.2.2.1
    have h2b0 : ind (i0 + b + b) = 0 := if_neg (by simpa [add_assoc] using hbar_2b i0 hi0)
    have hib_a : ind (i0 + b + a) = 0 := if_neg (by simpa [add_assoc, add_comm, add_left_comm] using hab_mem)
    have hib_ma : ind (i0 + b - a) = 0 := by
      apply if_neg
      intro hmem
      have hbad := hbar_2ab (i0 + b - a) hmem
      have heq : i0 + b - a + (a + a) - (b + b) = i0 + a - b := by abel
      rw [heq] at hbad; exact hbad hamb_mem
    have hib_mb : ind (i0 + b - b) = 1 := if_pos (by simpa using hi0)
    rw [hib0, h2b0, hib_a, hib_ma, hib_mb] at hib_eq
    omega

end GeneralCase

/- ## Section 3: Case 1 (`b + b = 0`) -/

section Case2bZero
variable {B V : Type*} [AddCommGroup B] [AddCommGroup V]
variable {a b : B} {x y : B → V}

/-- Voltage of the 4-cycle `Q(i) = (0,i)-0-(1,i)-b-(0,i+b)-0-(1,i+b)-b-(0,i)` when `b + b = 0`. -/
def qV (b : B) (y : B → V) (i : B) : V := y i + y (i + b)

/-- Under `b + b = 0` and `b ≠ 0`, `qV b y i = 0` gives an immediate 4-cycle `Q(i)`. -/
lemma case_2b_c4 (hb : b ≠ 0) (h2b : b + b = 0) (i : B) (hq : qV b y i = 0) :
    HasPow2 (GNorm a b x y) := by
  let f : Fin 4 → Bool × B × V := ![
    (false, i, 0), (true, i, 0), (false, i + b, -y (i + b)), (true, i + b, -y (i + b))]
  apply hasPow2_of_4 (walk_to_cycle (by decide) f ?_ ?_)
  · intro p q hpq
    fin_cases p <;> fin_cases q <;> dsimp [f] at hpq
    all_goals first
      | rfl
      | (solve | exfalso; have h := congrArg Prod.fst hpq; simp at h)
      | (have e := congrArg (fun z => z.2.1) hpq; dsimp at e
         first | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
               | (solve | exfalso; apply hb; linear_combination (norm := abel) -e))
  · intro k
    fin_cases k <;> dsimp [f]
    · exact e0 i 0
    · have e1 : i + b + b = i := by linear_combination (norm := abel) h2b
      simpa [e1, neg_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) (i + b) (-y (i + b))
    · exact e0 (i + b) (-y (i + b))
    · have hv : 0 + y i = -y (i + b) := by dsimp [qV] at hq; linear_combination (norm := abel) hq
      simpa [hv] using eb' (a := a) (b := b) (x := x) (y := y) i 0

/-- Under `b + b = 0` and `b ≠ 0`, `qV i ≠ 0` and `2 • qV i = 0` gives an 8-cycle (2x `Q(i)`). -/
lemma case_2b_c8 (hb : b ≠ 0) (h2b : b + b = 0) (i : B)
    (hq : qV b y i ≠ 0) (h2q : qV b y i + qV b y i = 0) :
    HasPow2 (GNorm a b x y) := by
  let q := qV b y i
  let f : Fin 8 → Bool × B × V := ![
    (false, i, 0), (true, i, 0), (false, i + b, -y (i + b)), (true, i + b, -y (i + b)),
    (false, i, -q), (true, i, -q), (false, i + b, -q - y (i + b)), (true, i + b, -q - y (i + b))]
  apply hasPow2_of_8 (walk_to_cycle (by decide) f ?_ ?_)
  · intro p r hpr
    fin_cases p <;> fin_cases r <;> dsimp [f] at hpr
    all_goals first
      | rfl
      | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
      | (have e := congrArg (fun z => z.2.1) hpr; dsimp at e
         first | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
               | (solve | exfalso; apply hb; linear_combination (norm := abel) -e))
      | (have e := congrArg (fun z => z.2.2) hpr; dsimp at e
         first | (solve | exfalso; apply hq; dsimp [q] at e; linear_combination (norm := abel) e)
               | (solve | exfalso; apply hq; dsimp [q] at e; linear_combination (norm := abel) -e))
  · intro k
    fin_cases k <;> dsimp [f]
    · exact e0 i 0
    · have e1 : i + b + b = i := by linear_combination (norm := abel) h2b
      simpa [e1, neg_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) (i + b) (-y (i + b))
    · exact e0 (i + b) (-y (i + b))
    · have hv : -q + y i = -y (i + b) := by dsimp [q, qV]; abel
      simpa [hv] using eb' (a := a) (b := b) (x := x) (y := y) i (-q)
    · exact e0 i (-q)
    · have e1 : i + b + b = i := by linear_combination (norm := abel) h2b
      simpa [e1, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) (i + b) (-q - y (i + b))
    · exact e0 (i + b) (-q - y (i + b))
    · have hv : 0 + y i = -q - y (i + b) := by
        dsimp [q, qV] at h2q ⊢; linear_combination (norm := abel) h2q
      simpa [hv] using eb' (a := a) (b := b) (x := x) (y := y) i 0

/-- The universal `H_8` lemma under `b + b = 0, a ≠ 0, b ≠ 0, a ≠ b`:
avoiding `HasPow2` forces either `(qV (i+a) = qV i ∧ hexV i = 0 ∧ hexV (i+b) = 0)`
or `(qV (i+a) = -qV i ∧ hexV i = -qV i)`. -/
lemma case_2b_H8 (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (h2b : b + b = 0)
    (hno : ¬ HasPow2 (GNorm a b x y)) (i : B) :
    (qV b y (i + a) = qV b y i ∧ hexV a b x y i = 0 ∧ hexV a b x y (i + b) = 0) ∨
    (qV b y (i + a) = -qV b y i ∧ hexV a b x y i = -qV b y i) := by
  -- Translate by i so we work at 0, b, a, a+b!
  have hno' : ¬ HasPow2 (GNorm a b (fun j => x (j + i)) (fun j => y (j + i))) :=
    fun h => hno (hasPow2_mono (gnorm_translate i) h)
  let x' := fun j => x (j + i)
  let y' := fun j => y (j + i)
  have hq0 : qV b y' 0 ≠ 0 := fun h => hno' (case_2b_c4 hb h2b 0 h)
  have hqa : qV b y' a ≠ 0 := fun h => hno' (case_2b_c4 hb h2b a h)
  have hab0 : a + b ≠ 0 := by
    intro e; exact hab (by linear_combination (norm := abel) e - h2b)
  -- Theta 1 in H_8: u0 = (false, 0), u1 = (false, b):
  -- P: (false,0) -0-> (true,0) -b'-> (false,b) [vP = -y' b]
  -- Q: (false,0) -b-> (true,b) -0'-> (false,b) [vQ = y' 0]
  -- R: (false,0) -a-> (true,a) -0'-> (false,a) -b-> (true,a+b) -a'-> (false,b) [vR = x' 0 + y' a - x' b]
  -- Check: vQ - vP = qV b y' 0 != 0!
  --        vR - vQ = hexV a b x' y' 0!
  --        vR - vP = hexV a b x' y' 0 + qV b y' 0!
  have hth1 : hexV a b x' y' 0 = 0 ∨ hexV a b x' y' 0 + qV b y' 0 = 0 := by
    by_contra hboth
    push_neg at hboth
    let u : Fin 7 → Bool × B := ![
      (false, 0), (false, b), (true, 0), (true, b), (true, a), (false, a), (true, a + b)]
    have hu : Function.Injective u := by
      intro p r hpr
      fin_cases p <;> fin_cases r <;> dsimp [u] at hpr
      all_goals first
        | rfl
        | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
        | (have e := congrArg Prod.snd hpr; dsimp at e
           first | (solve | exfalso; apply ha; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply ha; linear_combination (norm := abel) -e)
                 | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply hb; linear_combination (norm := abel) -e)
                 | (solve | exfalso; apply hab; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply hab; linear_combination (norm := abel) -e)
                 | (solve | exfalso; apply hab0; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply hab0; linear_combination (norm := abel) -e))
    let g : Fin 7 → V := ![0, 0, 0, y' 0, x' 0, x' 0, x' 0 + y' a]
    let vP : V := -y' b
    let vQ : V := y' 0
    let vR : V := x' 0 + y' a - x' b
    have hPQ : vP ≠ vQ := by
      intro e; exact hq0 (by dsimp [qV, vP, vQ] at e ⊢; rw [zero_add]; linear_combination (norm := abel) -e)
    have hQR : vQ ≠ vR := by
      intro e; exact hboth.1 (by dsimp [hexV, vQ, vR] at e ⊢; rw [zero_add, zero_add]; linear_combination (norm := abel) -e)
    have hRP : vR ≠ vP := by
      intro e; exact hboth.2 (by dsimp [hexV, qV, vR, vP] at e ⊢; rw [zero_add, zero_add]; linear_combination (norm := abel) e)
    apply hno'
    refine theta_2_2_4 u hu g vP vQ vR hPQ hQR hRP ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [u, g] using e0 (a := a) (b := b) (x := x') (y := y') 0 0
    · have e1 : b + b = 0 := h2b
      simpa [u, g, vP, e1, neg_add_cancel] using eb' (a := a) (b := b) (x := x') (y := y') b (-y' b)
    · simpa [u, g, zero_add] using eb (a := a) (b := b) (x := x') (y := y') 0 0
    · simpa [u, g, vQ] using e0' (a := a) (b := b) (x := x') (y := y') b (y' 0)
    · simpa [u, g, zero_add] using ea (a := a) (b := b) (x := x') (y := y') 0 0
    · simpa [u, g] using e0' (a := a) (b := b) (x := x') (y := y') a (x' 0)
    · simpa [u, g] using eb (a := a) (b := b) (x := x') (y := y') a (x' 0)
    · have e1 : b + a = a + b := add_comm _ _
      simpa [u, g, vR, e1, sub_add_cancel] using ea' (a := a) (b := b) (x := x') (y := y') b (x' 0 + y' a - x' b)
  -- Theta 2 in H_8: same u0=(false,0), u1=(false,b), P and Q, but R2 goes the OTHER way around Q(a):
  -- R2: (false,0) -a-> (true,a) -b'-> (false,a+b) -0-> (true,a+b) -a'-> (false,b) [vR2 = x' 0 - y' (a+b) - x' b]
  -- Check: vR2 - vQ = hexV 0 - qV a!
  --        vR2 - vP = hexV 0 - qV a + qV 0!
  have hth2 : hexV a b x' y' 0 - qV b y' a = 0 ∨ hexV a b x' y' 0 - qV b y' a + qV b y' 0 = 0 := by
    by_contra hboth
    push_neg at hboth
    let u : Fin 7 → Bool × B := ![
      (false, 0), (false, b), (true, 0), (true, b), (true, a), (false, a + b), (true, a + b)]
    have hu : Function.Injective u := by
      intro p r hpr
      fin_cases p <;> fin_cases r <;> dsimp [u] at hpr
      all_goals first
        | rfl
        | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
        | (have e := congrArg Prod.snd hpr; dsimp at e
           first | (solve | exfalso; apply ha; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply ha; linear_combination (norm := abel) -e)
                 | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply hb; linear_combination (norm := abel) -e)
                 | (solve | exfalso; apply hab; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply hab; linear_combination (norm := abel) -e)
                 | (solve | exfalso; apply hab0; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply hab0; linear_combination (norm := abel) -e))
    let g : Fin 7 → V := ![0, 0, 0, y' 0, x' 0, x' 0 - y' (a + b), x' 0 - y' (a + b)]
    let vP : V := -y' b
    let vQ : V := y' 0
    let vR : V := x' 0 - y' (a + b) - x' b
    have hPQ : vP ≠ vQ := by
      intro e; exact hq0 (by dsimp [qV, vP, vQ] at e ⊢; rw [zero_add]; linear_combination (norm := abel) -e)
    have hQR : vQ ≠ vR := by
      intro e; exact hboth.1 (by dsimp [hexV, qV, vQ, vR] at e ⊢; rw [zero_add, zero_add]; linear_combination (norm := abel) -e)
    have hRP : vR ≠ vP := by
      intro e; exact hboth.2 (by dsimp [hexV, qV, vR, vP] at e ⊢; rw [zero_add, zero_add]; linear_combination (norm := abel) e)
    apply hno'
    refine theta_2_2_4 u hu g vP vQ vR hPQ hQR hRP ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [u, g] using e0 (a := a) (b := b) (x := x') (y := y') 0 0
    · have e1 : b + b = 0 := h2b
      simpa [u, g, vP, e1, neg_add_cancel] using eb' (a := a) (b := b) (x := x') (y := y') b (-y' b)
    · simpa [u, g, zero_add] using eb (a := a) (b := b) (x := x') (y := y') 0 0
    · simpa [u, g, vQ] using e0' (a := a) (b := b) (x := x') (y := y') b (y' 0)
    · simpa [u, g, zero_add] using ea (a := a) (b := b) (x := x') (y := y') 0 0
    · have e1 : a + b + b = a := by linear_combination (norm := abel) h2b
      simpa [u, g, e1, sub_add_cancel] using eb' (a := a) (b := b) (x := x') (y := y') (a + b) (x' 0 - y' (a + b))
    · simpa [u, g] using e0 (a := a) (b := b) (x := x') (y := y') (a + b) (x' 0 - y' (a + b))
    · have e1 : b + a = a + b := add_comm _ _
      simpa [u, g, vR, e1, sub_add_cancel] using ea' (a := a) (b := b) (x := x') (y := y') b (x' 0 - y' (a + b) - x' b)
  -- Combine hth1 and hth2!
  have hsum_hex : hexV a b x' y' 0 + hexV a b x' y' b = qV b y' a - qV b y' 0 := by
    have e1 : b + b = 0 := h2b
    have e2 : b + a = a + b := add_comm _ _
    dsimp [hexV, qV]; simp only [zero_add, e1, e2]; abel
  -- Translate equations back from x', y' to x, y at i!
  have eq_q0 : qV b y' 0 = qV b y i := by simp [qV, y', add_comm]
  have eq_qa : qV b y' a = qV b y (i + a) := by
    simp [qV, y', add_assoc, add_comm, add_left_comm]
  have eq_h0 : hexV a b x' y' 0 = hexV a b x y i := by
    simp [hexV, x', y', add_assoc, add_comm, add_left_comm]
  have eq_hb : hexV a b x' y' b = hexV a b x y (i + b) := by
    simp [hexV, x', y', add_assoc, add_comm, add_left_comm]
  simp only [eq_q0, eq_qa, eq_h0] at hth1 hth2 hq0 hqa
  rw [eq_h0, eq_hb, eq_qa, eq_q0] at hsum_hex
  rcases hth1 with h1 | h1
  · rcases hth2 with h2 | h2
    · exact False.elim (hqa (by linear_combination (norm := abel) h1 - h2))
    · left
      have hqq : qV b y (i + a) = qV b y i := by linear_combination (norm := abel) h1 - h2
      refine ⟨hqq, h1, ?_⟩
      linear_combination (norm := abel) hsum_hex - h1 + hqq
  · rcases hth2 with h2 | h2
    · right
      have hqq : qV b y (i + a) = -qV b y i := by linear_combination (norm := abel) h1 - h2
      exact ⟨hqq, by linear_combination (norm := abel) h1⟩
    · exact False.elim (hqa (by linear_combination (norm := abel) h1 - h2))

/-- Subcase 1a: `b + b = 0` and `a + a = 0` (`Q_3` on `{0, b, a, a+b}`). -/
lemma case_2b_2a (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (h2b : b + b = 0) (h2a : a + a = 0) :
    HasPow2 (GNorm a b x y) := by
  classical
  by_contra hno
  have h0 := case_2b_H8 ha hb hab h2b hno 0
  have ha' := case_2b_H8 ha hb hab h2b hno a
  have h2a0 : a + a = 0 := h2a
  rw [zero_add] at h0
  rw [h2a0] at ha'
  rcases h0 with ⟨hq, hh0, hhb⟩ | ⟨hq, hh0⟩
  · -- qV a = qV 0 and hexV 0 = hexV b = 0.
    -- What about ha'? Since qV 0 = qV a, either hexV a = hexV (a+b) = 0 (done by all_hexV_zero on <a,b>!),
    -- OR qV 0 = -qV a (so 2*qV 0 = 0 -> 8-cycle!).
    rcases ha' with ⟨_, hha, hhab⟩ | ⟨hq2, _⟩
    · -- All 4 points 0, b, a, a+b have hexV = 0! Apply LocalCommutation.near0 at (0, 0)!
      have hma : (0 : B) - a = a := by linear_combination (norm := abel) -h2a
      have hmb : (0 : B) - b = b := by linear_combination (norm := abel) -h2b
      have hloc := local_comm_bound ha hb hab hno 0 hh0
      rw [zero_add] at hhb
      rw [zero_add, hma, zero_add, hmb, hha, hhb] at hloc
      simp at hloc
    · exact hno (case_2b_c8 hb h2b 0 (fun h => hno (case_2b_c4 hb h2b 0 h))
        (by linear_combination (norm := abel) hq2 - hq))
  · -- qV a = -qV 0 and hexV 0 = -qV 0 != 0!
    have hq0_nz : qV b y 0 ≠ 0 := fun h => hno (case_2b_c4 hb h2b 0 h)
    rcases ha' with ⟨hq2, _, _⟩ | ⟨_, hha⟩
    · exact hno (case_2b_c8 hb h2b 0 hq0_nz (by linear_combination (norm := abel) hq + hq2))
    · -- Now hexV 0 + hexV a = -qV 0 + (-qV a) = 0!
      have hsum : hexV a b x y 0 + hexV a b x y a = 0 := by
        rw [hh0, hha, hq]; abel
      -- Express hexV 0 + hexV a in terms of q_a(0) = x 0 + x a and q_a(b) = x b + x (a+b)!
      have hqa_eq : qV a x b = qV a x 0 := by
        dsimp [hexV, qV] at hsum ⊢
        have e1 : a + a = 0 := h2a
        have e2 : b + a = a + b := add_comm _ _
        simp only [zero_add, e1, e2] at hsum ⊢
        linear_combination (norm := abel) -hsum
      -- Now apply case_2b_H8 in the `a`-direction (via gnorm_swap_ab)!
      have hno_sw : ¬ HasPow2 (GNorm b a y x) := fun h => hno (hasPow2_mono gnorm_swap_ab h)
      have hsw := case_2b_H8 hb ha hab.symm h2a hno_sw 0
      rw [zero_add] at hsw
      rcases hsw with ⟨_, hhex0, _⟩ | ⟨hneg, _⟩
      · -- hexV b a y x 0 = 0 implies hexV a b x y 0 = 0, contradicting hexV 0 = -qV 0 != 0!
        have h00 : hexV a b x y 0 = 0 := by
          dsimp [hexV] at hhex0 ⊢; linear_combination (norm := abel) -hhex0
        exact hq0_nz (by linear_combination (norm := abel) hh0 - h00)
      · -- qV a x b = -qV a x 0 and qV a x b = qV a x 0 => 2 * qV a x 0 = 0 => 8-cycle!
        have hqa_nz : qV a x 0 ≠ 0 := fun h => hno_sw (case_2b_c4 ha h2a 0 h)
        exact hno_sw (case_2b_c8 ha h2a 0 hqa_nz (by linear_combination (norm := abel) hneg - hqa_eq))

/-- Subcase 1b: `b + b = 0` and `a + a = b` (`ℤ/4`, isomorphic to `Q_3`!). -/
lemma case_2b_2ab (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (h2b : b + b = 0) (h2ab : a + a = b) :
    HasPow2 (GNorm a b x y) := by
  -- Map GNorm on Z/2 x Z/2 (with generators (1,0), (0,1)) into GNorm a b x y via the exact Q_3 bijection:
  -- Left:  (0,0)->0, (0,1)->b, (1,0)->a+b, (1,1)->a
  -- Right: (0,0)->0, (0,1)->b, (1,0)->a,   (1,1)->a+b
  let B2 := ZMod 2 × ZMod 2
  let a2 : B2 := (1, 0)
  let b2 : B2 := (0, 1)
  let mapL : B2 → B := fun z =>
    if z.1 = 0 then (if z.2 = 0 then 0 else b) else (if z.2 = 0 then a + b else a)
  let mapR : B2 → B := fun z =>
    if z.1 = 0 then (if z.2 = 0 then 0 else b) else (if z.2 = 0 then a else a + b)
  have hab0 : a + b ≠ 0 := by intro e; exact hab (by linear_combination (norm := abel) e - h2b)
  have hmapL_inj : Function.Injective mapL := by
    intro u v huv
    have hu : u = (0, 0) ∨ u = (0, 1) ∨ u = (1, 0) ∨ u = (1, 1) := by clear huv; revert u; decide
    have hv : v = (0, 0) ∨ v = (0, 1) ∨ v = (1, 0) ∨ v = (1, 1) := by clear huv; revert v; decide
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
      simp only [mapL, one_ne_zero, ↓reduceIte] at huv
    all_goals first
      | rfl
      | (solve | exfalso; apply ha; linear_combination (norm := abel) huv)
      | (solve | exfalso; apply ha; linear_combination (norm := abel) -huv)
      | (solve | exfalso; apply hb; linear_combination (norm := abel) huv)
      | (solve | exfalso; apply hb; linear_combination (norm := abel) -huv)
      | (solve | exfalso; apply hab; linear_combination (norm := abel) huv)
      | (solve | exfalso; apply hab; linear_combination (norm := abel) -huv)
      | (solve | exfalso; apply hab0; linear_combination (norm := abel) huv)
      | (solve | exfalso; apply hab0; linear_combination (norm := abel) -huv)
  have hmapR_inj : Function.Injective mapR := by
    intro u v huv
    have hu : u = (0, 0) ∨ u = (0, 1) ∨ u = (1, 0) ∨ u = (1, 1) := by clear huv; revert u; decide
    have hv : v = (0, 0) ∨ v = (0, 1) ∨ v = (1, 0) ∨ v = (1, 1) := by clear huv; revert v; decide
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
      simp only [mapR, one_ne_zero, ↓reduceIte] at huv
    all_goals first
      | rfl
      | (solve | exfalso; apply ha; linear_combination (norm := abel) huv)
      | (solve | exfalso; apply ha; linear_combination (norm := abel) -huv)
      | (solve | exfalso; apply hb; linear_combination (norm := abel) huv)
      | (solve | exfalso; apply hb; linear_combination (norm := abel) -huv)
      | (solve | exfalso; apply hab; linear_combination (norm := abel) huv)
      | (solve | exfalso; apply hab; linear_combination (norm := abel) -huv)
      | (solve | exfalso; apply hab0; linear_combination (norm := abel) huv)
      | (solve | exfalso; apply hab0; linear_combination (norm := abel) -huv)
  -- Define weights w2 : B2 → Fin 3 → V matching edges of GNorm a b x y!
  -- From (0,0) [mapL=0]:   to (0,0) [0] (e0 0, 0),   to (1,0) [a] (ea 0, x 0),     to (0,1) [b] (eb 0, y 0)
  -- From (0,1) [mapL=b]:   to (0,1) [b] (e0 b, 0),   to (1,1) [a+b] (ea b, x b),   to (0,0) [0] (eb b, y b)
  -- From (1,0) [mapL=a+b]: to (1,0) [a] (eb (a+b), y(a+b)), to (0,0) [0] (ea (a+b), x(a+b)), to (1,1) [a+b] (e0 (a+b), 0)
  -- From (1,1) [mapL=a]:   to (1,1) [a+b] (eb a, y a), to (0,1) [b] (ea a, x a),   to (1,0) [a] (e0 a, 0)
  let w2 : B2 → Fin 3 → V := fun z k =>
    if z.1 = 0 then
      if z.2 = 0 then ![0, x 0, y 0] k else ![0, x b, y b] k
    else
      if z.2 = 0 then ![y (a + b), x (a + b), 0] k else ![y a, x a, 0] k
  let G2 := SimpleGraph.fromRel fun l r : Bool × B2 × V =>
    ∃ (i : B2) (k : Fin 3) (g : V),
      l = (false, i, g) ∧ r = (true, i + (![0, a2, b2] : Fin 3 → B2) k, g + w2 i k)
  let emb : (Bool × B2 × V) ↪ (Bool × B × V) :=
    { toFun := fun z => (z.1, if z.1 then mapR z.2.1 else mapL z.2.1, z.2.2)
      inj' := by
        rintro ⟨s1, i1, g1⟩ ⟨s2, i2, g2⟩ h
        cases s1 <;> cases s2 <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
        · exact Prod.ext rfl (Prod.ext (hmapL_inj h.2.1) h.2.2)
        · exact False.elim (absurd h.1 (by decide))
        · exact False.elim (absurd h.1 (by decide))
        · exact Prod.ext rfl (Prod.ext (hmapR_inj h.2.1) h.2.2) }
  have hG2 : G2 ⊑ GNorm a b x y := by
    refine ⟨⟨⟨emb, ?_⟩, emb.injective⟩⟩
    have fwd : ∀ (i : B2) (k : Fin 3) (g : V),
        (GNorm a b x y).Adj (emb (false, i, g))
          (emb (true, i + (![0, a2, b2] : Fin 3 → B2) k, g + w2 i k)) := by
      intro i k g
      have hba : b + a = a + b := add_comm _ _
      have haba : a + b + a = 0 := by linear_combination (norm := abel) h2ab + h2b
      have habb : a + b + b = a := by linear_combination (norm := abel) h2b
      have hi : i = (0, 0) ∨ i = (0, 1) ∨ i = (1, 0) ∨ i = (1, 1) := by revert i; decide
      change (GNorm a b x y).Adj (false, mapL i, g)
        (true, mapR (i.1 + ((![0, a2, b2] : Fin 3 → B2) k).1, i.2 + ((![0, a2, b2] : Fin 3 → B2) k).2), g + w2 i k)
      rcases hi with rfl | rfl | rfl | rfl <;> fin_cases k <;>
        dsimp [mapL, mapR, w2, a2, b2] <;>
        (try simp only [add_zero, zero_add, ↓reduceIte,
          one_ne_zero, show (1 : ZMod 2) + 1 = 0 by decide])
      · simpa using e0 (a := a) (b := b) (x := x) (y := y) 0 g
      · simpa using ea (a := a) (b := b) (x := x) (y := y) 0 g
      · simpa using eb (a := a) (b := b) (x := x) (y := y) 0 g
      · simpa using e0 (a := a) (b := b) (x := x) (y := y) b g
      · simpa [hba] using ea (a := a) (b := b) (x := x) (y := y) b g
      · simpa [h2b] using eb (a := a) (b := b) (x := x) (y := y) b g
      · simpa [habb] using eb (a := a) (b := b) (x := x) (y := y) (a + b) g
      · simpa [haba] using ea (a := a) (b := b) (x := x) (y := y) (a + b) g
      · simpa using e0 (a := a) (b := b) (x := x) (y := y) (a + b) g
      · simpa using eb (a := a) (b := b) (x := x) (y := y) a g
      · simpa [h2ab] using ea (a := a) (b := b) (x := x) (y := y) a g
      · simpa using e0 (a := a) (b := b) (x := x) (y := y) a g
    intro u v huv
    rcases huv with ⟨_, hr | hr⟩
    · rcases hr with ⟨i, k, g, rfl, rfl⟩; exact fwd i k g
    · rcases hr with ⟨i, k, g, rfl, rfl⟩; exact (fwd i k g).symm
  apply hasPow2_mono ( (gnorm_le_orig a2 b2 w2).trans hG2 )
  exact case_2b_2a (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Subcase 1c: `b + b = 0` and `a + a ≠ 0` and `a + a ≠ b` (`H_12` on 3 columns `0, a, 2a`). -/
lemma case_2b_H12 (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (h2b : b + b = 0)
    (h2a : a + a ≠ 0) (h2ab : a + a ≠ b) : HasPow2 (GNorm a b x y) := by
  by_contra hno
  have h0 := case_2b_H8 ha hb hab h2b hno 0
  have ha' := case_2b_H8 ha hb hab h2b hno a
  rw [zero_add] at h0
  have hq0 : qV b y 0 ≠ 0 := fun h => hno (case_2b_c4 hb h2b 0 h)
  have hab0 : a + b ≠ 0 := by intro e; exact hab (by linear_combination (norm := abel) e - h2b)
  have h2ab0 : a + a + b ≠ 0 := by intro e; exact h2ab (by linear_combination (norm := abel) e - h2b)
  -- The 6 base elements 0, b, a, a+b, 2a, 2a+b are pairwise distinct!
  let col : Fin 6 → B := ![0, b, a, a + b, a + a, a + a + b]
  have hcol : Function.Injective col := by
    intro p r hpr
    fin_cases p <;> fin_cases r <;> dsimp [col] at hpr
    all_goals first
      | rfl
      | (solve | exfalso; apply ha; linear_combination (norm := abel) hpr)
      | (solve | exfalso; apply ha; linear_combination (norm := abel) -hpr)
      | (solve | exfalso; apply hb; linear_combination (norm := abel) hpr)
      | (solve | exfalso; apply hb; linear_combination (norm := abel) -hpr)
      | (solve | exfalso; apply hab; linear_combination (norm := abel) hpr)
      | (solve | exfalso; apply hab; linear_combination (norm := abel) -hpr)
      | (solve | exfalso; apply hab0; linear_combination (norm := abel) hpr)
      | (solve | exfalso; apply hab0; linear_combination (norm := abel) -hpr)
      | (solve | exfalso; apply h2a; linear_combination (norm := abel) hpr)
      | (solve | exfalso; apply h2a; linear_combination (norm := abel) -hpr)
      | (solve | exfalso; apply h2ab; linear_combination (norm := abel) hpr)
      | (solve | exfalso; apply h2ab; linear_combination (norm := abel) -hpr)
      | (solve | exfalso; apply h2ab0; linear_combination (norm := abel) hpr)
      | (solve | exfalso; apply h2ab0; linear_combination (norm := abel) -hpr)
  -- Build a unified helper for our 3 explicit 16-cycles in H_12!
  -- Each walk is given by idx : Fin 16 → Bool × Fin 6 and g : Fin 16 → V,
  -- where the ONLY repeated base vertices have voltage diff ± qV b y 0!
  have mk16 : ∀ (w : Fin 16 → Bool × Fin 6) (gv : Fin 16 → V)
      (cols : List (Fin 16 × Fin 16)),
      (∀ i j : Fin 16, i < j → w i = w j → (i, j) ∈ cols) →
      (∀ p ∈ cols, gv p.1 ≠ gv p.2) →
      (∀ i : Fin 16, (GNorm a b x y).Adj
        ((w i).1, col (w i).2, gv i) ((w (i + 1)).1, col (w (i + 1)).2, gv (i + 1))) →
      False := by
    intro w gv cols hcols hdiff hstep
    apply hno; apply hasPow2_of_16
    refine walk_to_cycle (by decide) (fun i => ((w i).1, col (w i).2, gv i)) ?_ hstep
    intro i j hij
    by_contra hne
    have hw : w i = w j := Prod.ext (congrArg (fun z : Bool × B × V => z.1) hij)
      (hcol (congrArg (fun z : Bool × B × V => z.2.1) hij))
    have hg : gv i = gv j := congrArg (fun z : Bool × B × V => z.2.2) hij
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hdiff (i, j) (hcols i j hlt hw) hg
    · exact hdiff (j, i) (hcols j i hlt hw.symm) hg.symm
  -- Helper edge lemmas on col indices:
  have ec0 : ∀ (k : Fin 6) (g : V), (GNorm a b x y).Adj (false, col k, g) (true, col k, g) :=
    fun k g => e0 (col k) g
  have hba : b + a = a + b := add_comm _ _
  have h2ba : a + b + a = a + a + b := by abel
  have hbb : a + b + b = a := by linear_combination (norm := abel) h2b
  have h2bb : a + a + b + b = a + a := by linear_combination (norm := abel) h2b
  -- Note: for each of the 4 cases of (h0, ha'), we give an explicit 16-cycle in H_12!
  -- Wait: case (s1 = -1, s2 = +1) is the same walk as (s1 = +1, s2 = -1) or directly checked!
  -- Let's check all 4 combinations!
  let q := qV b y 0
  have hq_def : y 0 + y b = q := by simp [q, qV]
  rcases h0 with ⟨hq1, hh0, _⟩ | ⟨hq1, hh0⟩
  · rcases ha' with ⟨hq2, hha, _⟩ | ⟨hq2, hha⟩
    · -- Case (+1, +1): qV a = q, qV (2a) = q, hexV 0 = 0, hexV a = 0!
      -- Walk: (0,0)-(1,0)-(0,1)-(1,1)-(0,0)-(1,0)-(0,1)-(1,3)-(0,3)-(1,2)-(0,2)-(1,4)-(0,4)-(1,5)-(0,3)-(1,2)
      -- Wait: (0,0)-(1,0)-(0,1)-(1,1)-(0,0) goes around Q(0) [volt -q], then (0,0)-(1,0)-(0,1) [volt -y b],
      -- then (0,1)-a->(1,3) [+x b], (1,3)-0->(0,3), (0,3)-b->(1,2) [+y(a+b)], (1,2)-0->(0,2),
      -- (0,2)-a->(1,4) [+x a], (1,4)-0->(0,4), (0,4)-b->(1,5) [+y(2a)], (1,5)-a->(0,3) [-x(a+b)],
      -- (0,3)-b->(1,2)? Wait: (0,3)-(1,2) was already used!
      -- Wait: look at the walk printed by Python for (1,1,1,0,0):
      -- [(0,0),(1,0),(0,1),(1,1),(0,0),(1,0),(0,1),(1,3),(0,3),(1,2),(0,2),(1,4),(0,4),(1,5),(0,3),(1,2)]
      -- Wait: step 15->0 is (1,2) -> (0,0) which is ea' 0!
      -- Step 13->14 is (1,5) -> (0,3) which is ea' (a+b)!
      -- Step 14->15 is (0,3) -> (1,2) which is eb (a+b) — at a DIFFERENT voltage (shifted by q)!
      let w : Fin 16 → Bool × Fin 6 := ![
        (false, 0), (true, 0), (false, 1), (true, 1),
        (false, 0), (true, 0), (false, 1), (true, 3),
        (false, 3), (true, 2), (false, 2), (true, 4),
        (false, 4), (true, 5), (false, 3), (true, 2)]
      let g0 : V := 0
      let g1 : V := 0
      let g2 : V := -y b
      let g3 : V := -y b
      let g4 : V := -q
      let g5 : V := -q
      let g6 : V := -q - y b
      let g7 : V := -q - y b + x b
      let g8 : V := -q - y b + x b
      let g9 : V := -q - y b + x b + y (a + b)
      let g10 : V := -q - y b + x b + y (a + b)
      let g11 : V := -q - y b + x b + y (a + b) + x a
      let g12 : V := -q - y b + x b + y (a + b) + x a
      let g13 : V := -q - y b + x b + y (a + b) + x a + y (a + a)
      let g14 : V := -q - y b + x b + y (a + b) + x a + y (a + a) - x (a + b)
      let g15 : V := x 0
      let gv : Fin 16 → V := ![g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15]
      have h_g14_g8 : g14 - g8 = q := by
        dsimp [g14, g8, q, qV]; dsimp [hexV, qV] at hha hq1; simp only [zero_add] at hq1 ⊢
        linear_combination (norm := abel) hha + hq1
      have h_g15_g9 : g15 - g9 = q := by
        dsimp [g15, g9, q, qV]; dsimp [hexV, qV] at hh0 hq1; simp only [zero_add] at hh0 hq1 ⊢
        linear_combination (norm := abel) hh0 - hq1
      have h_step14 : g14 + y (a + b) = g15 := by
        have h98 : g9 = g8 + y (a + b) := rfl
        linear_combination (norm := abel) h_g14_g8 - h_g15_g9 - h98
      apply mk16 w gv [(0, 4), (1, 5), (2, 6), (8, 14), (9, 15)] (by decide)
      · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp [gv] <;> intro e
        · apply hq0; dsimp [g0, g4, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [g1, g5, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [g2, g6, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [q] at h_g14_g8; linear_combination (norm := abel) -h_g14_g8 - e
        · apply hq0; dsimp [q] at h_g15_g9; linear_combination (norm := abel) -h_g15_g9 - e
      · intro i
        fin_cases i <;> dsimp [w, col, gv]
        · exact e0 0 g0
        · simpa [g1, g2, h2b, neg_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) b (-y b)
        · exact e0 b g2
        · have hv : g4 + y 0 = g3 := by dsimp [g4, g3, q, qV]; rw [zero_add]; abel
          simpa [hv] using eb' (a := a) (b := b) (x := x) (y := y) 0 g4
        · exact e0 0 g4
        · simpa [g5, g6, h2b, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) b (-q - y b)
        · simpa [g6, g7, hba] using ea (a := a) (b := b) (x := x) (y := y) b g6
        · exact e0' (a + b) g7
        · simpa [g8, g9, hbb] using eb (a := a) (b := b) (x := x) (y := y) (a + b) g8
        · exact e0' a g9
        · simpa [g10, g11] using ea (a := a) (b := b) (x := x) (y := y) a g10
        · exact e0' (a + a) g11
        · simpa [g12, g13] using eb (a := a) (b := b) (x := x) (y := y) (a + a) g12
        · simpa [g13, g14, h2ba, sub_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) (a + b) g14
        · simpa [hbb, h_step14] using eb (a := a) (b := b) (x := x) (y := y) (a + b) g14
        · simpa [g15, g0, zero_add] using ea' (a := a) (b := b) (x := x) (y := y) 0 0
    · -- Case (+1, -1): qV a = q, qV (2a) = -q, hexV 0 = 0, hexV a = -q!
      -- Walk: (0,0),(1,0),(0,1),(1,1),(0,0),(1,0),(0,1),(1,3),(0,3),(1,2),(0,2),(1,4),(0,5),(1,5),(0,3),(1,2)
      let w : Fin 16 → Bool × Fin 6 := ![
        (false, 0), (true, 0), (false, 1), (true, 1),
        (false, 0), (true, 0), (false, 1), (true, 3),
        (false, 3), (true, 2), (false, 2), (true, 4),
        (false, 5), (true, 5), (false, 3), (true, 2)]
      let g0 : V := 0
      let g1 : V := 0
      let g2 : V := -y b
      let g3 : V := -y b
      let g4 : V := -q
      let g5 : V := -q
      let g6 : V := -q - y b
      let g7 : V := -q - y b + x b
      let g8 : V := -q - y b + x b
      let g9 : V := -q - y b + x b + y (a + b)
      let g10 : V := -q - y b + x b + y (a + b)
      let g11 : V := -q - y b + x b + y (a + b) + x a
      let g12 : V := -q - y b + x b + y (a + b) + x a - y (a + a + b)
      let g13 : V := -q - y b + x b + y (a + b) + x a - y (a + a + b)
      let g14 : V := -q - y b + x b + y (a + b) + x a - y (a + a + b) - x (a + b)
      let g15 : V := x 0
      let gv : Fin 16 → V := ![g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15]
      have h_g14_g8 : g14 - g8 = q := by
        dsimp [g14, g8, q, qV]; dsimp [hexV, qV] at hha hq1 hq2; simp only [zero_add] at hq1 ⊢
        linear_combination (norm := abel) hha - hq2 + hq1
      have h_g15_g9 : g15 - g9 = q := by
        dsimp [g15, g9, q, qV]; dsimp [hexV, qV] at hh0 hq1; simp only [zero_add] at hh0 hq1 ⊢
        linear_combination (norm := abel) hh0 - hq1
      have h_step14 : g14 + y (a + b) = g15 := by
        have h98 : g9 = g8 + y (a + b) := rfl
        linear_combination (norm := abel) h_g14_g8 - h_g15_g9 - h98
      apply mk16 w gv [(0, 4), (1, 5), (2, 6), (8, 14), (9, 15)] (by decide)
      · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp [gv] <;> intro e
        · apply hq0; dsimp [g0, g4, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [g1, g5, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [g2, g6, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [q] at h_g14_g8; linear_combination (norm := abel) -h_g14_g8 - e
        · apply hq0; dsimp [q] at h_g15_g9; linear_combination (norm := abel) -h_g15_g9 - e
      · intro i
        fin_cases i <;> dsimp [w, col, gv]
        · exact e0 0 g0
        · simpa [g1, g2, h2b, neg_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) b (-y b)
        · exact e0 b g2
        · have hv : g4 + y 0 = g3 := by dsimp [g4, g3, q, qV]; rw [zero_add]; abel
          simpa [hv] using eb' (a := a) (b := b) (x := x) (y := y) 0 g4
        · exact e0 0 g4
        · simpa [g5, g6, h2b, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) b (-q - y b)
        · simpa [g6, g7, hba] using ea (a := a) (b := b) (x := x) (y := y) b g6
        · exact e0' (a + b) g7
        · simpa [g8, g9, hbb] using eb (a := a) (b := b) (x := x) (y := y) (a + b) g8
        · exact e0' a g9
        · simpa [g10, g11] using ea (a := a) (b := b) (x := x) (y := y) a g10
        · simpa [g11, g12, h2bb, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) (a + a + b) g12
        · exact e0 (a + a + b) g12
        · simpa [g13, g14, h2ba, sub_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) (a + b) g14
        · simpa [hbb, h_step14] using eb (a := a) (b := b) (x := x) (y := y) (a + b) g14
        · simpa [g15, g0, zero_add] using ea' (a := a) (b := b) (x := x) (y := y) 0 0
  · rcases ha' with ⟨hq2, hha, _⟩ | ⟨hq2, hha⟩
    · -- Case (-1, +1): qV a = -q, qV (2a) = -q, hexV 0 = -q, hexV a = 0!
      -- Walk: (0,0),(1,0),(0,1),(1,1),(0,0),(1,0),(0,1),(1,3),(0,2),(1,2),(0,3),(1,5),(0,4),(1,4),(0,2),(1,2)
      let w : Fin 16 → Bool × Fin 6 := ![
        (false, 0), (true, 0), (false, 1), (true, 1),
        (false, 0), (true, 0), (false, 1), (true, 3),
        (false, 2), (true, 2), (false, 3), (true, 5),
        (false, 4), (true, 4), (false, 2), (true, 2)]
      let g0 : V := 0
      let g1 : V := 0
      let g2 : V := -y b
      let g3 : V := -y b
      let g4 : V := -q
      let g5 : V := -q
      let g6 : V := -q - y b
      let g7 : V := -q - y b + x b
      let g8 : V := -q - y b + x b - y a
      let g9 : V := -q - y b + x b - y a
      let g10 : V := -q - y b + x b - y a - y (a + b)
      let g11 : V := -q - y b + x b - y a - y (a + b) + x (a + b)
      let g12 : V := -q - y b + x b - y a - y (a + b) + x (a + b) - y (a + a)
      let g13 : V := -q - y b + x b - y a - y (a + b) + x (a + b) - y (a + a)
      let g14 : V := -q - y b + x b - y a - y (a + b) + x (a + b) - y (a + a) - x a
      let g15 : V := x 0
      let gv : Fin 16 → V := ![g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15]
      have h_g14_g8 : g14 - g8 = q := by
        dsimp [g14, g8, q, qV]; dsimp [hexV, qV] at hha hq1; simp only [zero_add] at hq1 ⊢
        linear_combination (norm := abel) -hha - hq1
      have h_g15_g9 : g15 - g9 = q := by
        dsimp [g15, g9, q, qV]; dsimp [hexV, qV] at hh0; simp only [zero_add] at hh0 ⊢
        linear_combination (norm := abel) hh0
      have h_step14 : g14 = g15 := by
        have h98 : g9 = g8 := rfl
        linear_combination (norm := abel) h_g14_g8 - h_g15_g9 + h98
      apply mk16 w gv [(0, 4), (1, 5), (2, 6), (8, 14), (9, 15)] (by decide)
      · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp [gv] <;> intro e
        · apply hq0; dsimp [g0, g4, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [g1, g5, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [g2, g6, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [q] at h_g14_g8; linear_combination (norm := abel) -h_g14_g8 - e
        · apply hq0; dsimp [q] at h_g15_g9; linear_combination (norm := abel) -h_g15_g9 - e
      · intro i
        fin_cases i <;> dsimp [w, col, gv]
        · exact e0 0 g0
        · simpa [g1, g2, h2b, neg_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) b (-y b)
        · exact e0 b g2
        · have hv : g4 + y 0 = g3 := by dsimp [g4, g3, q, qV]; rw [zero_add]; abel
          simpa [hv] using eb' (a := a) (b := b) (x := x) (y := y) 0 g4
        · exact e0 0 g4
        · simpa [g5, g6, h2b, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) b (-q - y b)
        · simpa [g6, g7, hba] using ea (a := a) (b := b) (x := x) (y := y) b g6
        · simpa [g7, g8, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) a g8
        · exact e0 a g8
        · simpa [g9, g10, hbb, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) (a + b) g10
        · simpa [g10, g11, h2ba] using ea (a := a) (b := b) (x := x) (y := y) (a + b) g10
        · simpa [g11, g12, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) (a + a) g12
        · exact e0 (a + a) g12
        · simpa [g13, g14, sub_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) a g14
        · simpa [h_step14] using e0 (a := a) (b := b) (x := x) (y := y) a g14
        · simpa [g15, g0, zero_add] using ea' (a := a) (b := b) (x := x) (y := y) 0 0
    · -- Case (-1, -1): qV a = -q, qV (2a) = q, hexV 0 = -q, hexV a = q!
      -- Walk: (0,0),(1,0),(0,1),(1,1),(0,0),(1,0),(0,1),(1,3),(0,2),(1,2),(0,3),(1,5),(0,5),(1,4),(0,2),(1,2)
      let w : Fin 16 → Bool × Fin 6 := ![
        (false, 0), (true, 0), (false, 1), (true, 1),
        (false, 0), (true, 0), (false, 1), (true, 3),
        (false, 2), (true, 2), (false, 3), (true, 5),
        (false, 5), (true, 4), (false, 2), (true, 2)]
      let g0 : V := 0
      let g1 : V := 0
      let g2 : V := -y b
      let g3 : V := -y b
      let g4 : V := -q
      let g5 : V := -q
      let g6 : V := -q - y b
      let g7 : V := -q - y b + x b
      let g8 : V := -q - y b + x b - y a
      let g9 : V := -q - y b + x b - y a
      let g10 : V := -q - y b + x b - y a - y (a + b)
      let g11 : V := -q - y b + x b - y a - y (a + b) + x (a + b)
      let g12 : V := -q - y b + x b - y a - y (a + b) + x (a + b)
      let g13 : V := -q - y b + x b - y a - y (a + b) + x (a + b) + y (a + a + b)
      let g14 : V := -q - y b + x b - y a - y (a + b) + x (a + b) + y (a + a + b) - x a
      let g15 : V := x 0
      let gv : Fin 16 → V := ![g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15]
      have h_g14_g8 : g14 - g8 = q := by
        dsimp [g14, g8, q, qV]; dsimp [hexV, qV] at hha hq1 hq2; simp only [zero_add] at hq1 ⊢
        linear_combination (norm := abel) -hha + hq2 - hq1
      have h_g15_g9 : g15 - g9 = q := by
        dsimp [g15, g9, q, qV]; dsimp [hexV, qV] at hh0; simp only [zero_add] at hh0 ⊢
        linear_combination (norm := abel) hh0
      have h_step14 : g14 = g15 := by
        have h98 : g9 = g8 := rfl
        linear_combination (norm := abel) h_g14_g8 - h_g15_g9 + h98
      apply mk16 w gv [(0, 4), (1, 5), (2, 6), (8, 14), (9, 15)] (by decide)
      · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp [gv] <;> intro e
        · apply hq0; dsimp [g0, g4, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [g1, g5, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [g2, g6, q] at e; linear_combination (norm := abel) e
        · apply hq0; dsimp [q] at h_g14_g8; linear_combination (norm := abel) -h_g14_g8 - e
        · apply hq0; dsimp [q] at h_g15_g9; linear_combination (norm := abel) -h_g15_g9 - e
      · intro i
        fin_cases i <;> dsimp [w, col, gv]
        · exact e0 0 g0
        · simpa [g1, g2, h2b, neg_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) b (-y b)
        · exact e0 b g2
        · have hv : g4 + y 0 = g3 := by dsimp [g4, g3, q, qV]; rw [zero_add]; abel
          simpa [hv] using eb' (a := a) (b := b) (x := x) (y := y) 0 g4
        · exact e0 0 g4
        · simpa [g5, g6, h2b, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) b (-q - y b)
        · simpa [g6, g7, hba] using ea (a := a) (b := b) (x := x) (y := y) b g6
        · simpa [g7, g8, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) a g8
        · exact e0 a g8
        · simpa [g9, g10, hbb, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) (a + b) g10
        · simpa [g10, g11, h2ba] using ea (a := a) (b := b) (x := x) (y := y) (a + b) g10
        · exact e0' (a + a + b) g11
        · simpa [g12, g13, h2bb] using eb (a := a) (b := b) (x := x) (y := y) (a + a + b) g12
        · simpa [g13, g14, sub_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) a g14
        · simpa [h_step14] using e0 (a := a) (b := b) (x := x) (y := y) a g14
        · simpa [g15, g0, zero_add] using ea' (a := a) (b := b) (x := x) (y := y) 0 0

/-- Complete proof of Case 1 (`b + b = 0`). -/
theorem case_2b_zero (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (h2b : b + b = 0) :
    HasPow2 (GNorm a b x y) := by
  by_cases h2a : a + a = 0
  · exact case_2b_2a ha hb hab h2b h2a
  · by_cases h2ab : a + a = b
    · exact case_2b_2ab ha hb hab h2b h2ab
    · exact case_2b_H12 ha hb hab h2b h2a h2ab

end Case2bZero

/- ## Section 4: Case 2 (`a = 2 • b`) -/

section CaseA2b
variable {B V : Type*} [AddCommGroup B] [AddCommGroup V]
variable {a b : B} {x y : B → V}

/-- Voltage of the 4-cycle `Q(i) = (0,i)-b->(1,i+b)-0->(0,i+b)-b->(1,i+2b)-a->(0,i)` when `a = 2 • b`. -/
def q2V (b : B) (x y : B → V) (i : B) : V := y i + y (i + b) - x i

/-- Under `a = 2 • b` and `b ≠ 0`, `q2V b x y i = 0` gives an immediate 4-cycle. -/
lemma case_a2b_c4 (hb : b ≠ 0) (ha2b : a = 2 • b) (h2b : 2 • b ≠ 0) (i : B)
    (hq : q2V b x y i = 0) : HasPow2 (GNorm a b x y) := by
  let f : Fin 4 → Bool × B × V := ![
    (false, i, 0), (true, i + b, y i), (false, i + b, y i), (true, i + 2 • b, y i + y (i + b))]
  apply hasPow2_of_4 (walk_to_cycle (by decide) f ?_ ?_)
  · intro p r hpr
    fin_cases p <;> fin_cases r <;> dsimp [f] at hpr
    all_goals first
      | rfl
      | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
      | (have e := congrArg (fun z => z.2.1) hpr; dsimp at e
         first | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
               | (solve | exfalso; apply hb; linear_combination (norm := abel) -e))
  · intro k
    fin_cases k <;> dsimp [f]
    · simpa using eb (a := a) (b := b) (x := x) (y := y) i 0
    · exact e0' (i + b) (y i)
    · have e1 : i + b + b = i + 2 • b := by abel
      simpa [e1] using eb (a := a) (b := b) (x := x) (y := y) (i + b) (y i)
    · have hv : 0 + x i = y i + y (i + b) := by
        dsimp [q2V] at hq; linear_combination (norm := abel) -hq
      simpa [ha2b, hv] using ea' (a := a) (b := b) (x := x) (y := y) i 0

/-- Subcase 2a: `a = 2 • b` and `3 • b = 0` (`K_{3,3}`), proved by 2-subdivision of `HaarShort`
inside `K_{2,3} ⊆ K_{3,3}`! -/
lemma case_a2b_k33 (hb : b ≠ 0) (ha2b : a = 2 • b) (h3b : 3 • b = 0) :
    HasPow2 (GNorm a b x y) := by
  classical
  have h2b : 2 • b ≠ 0 := by
    intro e; exact hb (by linear_combination (norm := abel) h3b - e)
  -- Three 2-paths between (false, 0) and (false, b):
  --   P0: (false, 0, g) --0--> (true, 0, g) <--a-- (false, b, g - x b)   [since b + 2b = 0]
  --   P1: (false, 0, g) --b--> (true, b, g + y 0) <--0-- (false, b, g + y 0)
  --   P2: (false, 0, g) --a--> (true, 2b, g + x 0) <--b-- (false, b, g + x 0 - y b)
  -- Shift (false, b, g) by -x b so P0 has shift 0, P1 has shift u = y 0 + x b, P2 has shift v = x 0 - y b + x b!
  let u : V := y 0 + x b
  let v : V := x 0 - y b + x b
  by_cases hu : u = 0
  · -- P0 and P1 form a 4-cycle!
    let f : Fin 4 → Bool × B × V := ![
      (false, 0, 0), (true, 0, 0), (false, b, -x b), (true, b, -x b)]
    apply hasPow2_of_4 (walk_to_cycle (by decide) f ?_ ?_)
    · intro p r hpr
      fin_cases p <;> fin_cases r <;> dsimp [f] at hpr
      all_goals
        first
        | rfl
        | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
        | (have e := congrArg (fun z => z.2.1) hpr; dsimp at e
           first | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply hb; linear_combination (norm := abel) -e))
    · intro k; fin_cases k <;> dsimp [f]
      · exact e0 0 0
      · have e1 : b + a = 0 := by rw [ha2b]; linear_combination (norm := abel) h3b
        simpa [e1, neg_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) b (-x b)
      · exact e0 b (-x b)
      · have hv : 0 + y 0 = -x b := by dsimp [u] at hu; linear_combination (norm := abel) hu
        simpa [zero_add, hv] using eb' (a := a) (b := b) (x := x) (y := y) 0 0
  by_cases hv : v = 0
  · -- P0 and P2 form a 4-cycle!
    let f : Fin 4 → Bool × B × V := ![
      (false, 0, 0), (true, 0, 0), (false, b, -x b), (true, 2 • b, x 0)]
    apply hasPow2_of_4 (walk_to_cycle (by decide) f ?_ ?_)
    · intro p r hpr
      fin_cases p <;> fin_cases r <;> dsimp [f] at hpr
      all_goals
        first
        | rfl
        | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
        | (have e := congrArg (fun z => z.2.1) hpr; dsimp at e
           first | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply hb; linear_combination (norm := abel) -e)
                 | (solve | exfalso; apply h2b; linear_combination (norm := abel) e)
                 | (solve | exfalso; apply h2b; linear_combination (norm := abel) -e))
    · intro k; fin_cases k <;> dsimp [f]
      · exact e0 0 0
      · have e1 : b + a = 0 := by rw [ha2b]; linear_combination (norm := abel) h3b
        simpa [e1, neg_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) b (-x b)
      · have e1 : b + b = 2 • b := by abel
        have hvv : -x b + y b = x 0 := by dsimp [v] at hv; linear_combination (norm := abel) -hv
        simpa [e1, hvv] using eb (a := a) (b := b) (x := x) (y := y) b (-x b)
      · simpa [ha2b, zero_add] using ea' (a := a) (b := b) (x := x) (y := y) 0 0
  by_cases huv : u = v
  · -- P1 and P2 form a 4-cycle (which is Q(0))!
    exact case_a2b_c4 hb ha2b h2b 0 (by dsimp [q2V, u, v] at huv ⊢; rw [zero_add]; linear_combination (norm := abel) huv)
  · -- Apply HaarShort.haar_short_cycle to H on Bool × V with shifts 0, u, v!
    let H : SimpleGraph (Bool × V) := SimpleGraph.fromRel fun l r =>
      l.1 = false ∧ r.1 = true ∧ (r.2 = l.2 ∨ r.2 = l.2 + u ∨ r.2 = l.2 + v)
    have hH0 : ∀ g, H.Adj (false, g) (true, g) := fun g => ⟨by simp, .inl ⟨rfl, rfl, .inl rfl⟩⟩
    have hH1 : ∀ g, H.Adj (false, g) (true, g + u) := fun g => ⟨by simp, .inl ⟨rfl, rfl, .inr (.inl rfl)⟩⟩
    have hH2 : ∀ g, H.Adj (false, g) (true, g + v) := fun g => ⟨by simp, .inl ⟨rfl, rfl, .inr (.inr rfl)⟩⟩
    have hshort := HaarShort.haar_short_cycle H u v hu hv huv hH0 hH1 hH2
    -- Subdivide any cycle of length n (n ≥ 4) in H into a cycle of length 2*n in GNorm!
    have subdiv : ∀ {n : ℕ}, 4 ≤ n → cycleGraph n ⊑ H → cycleGraph (2 * n) ⊑ GNorm a b x y := by
      intro n hn ⟨c⟩
      haveI : NeZero n := ⟨by omega⟩
      haveI : NeZero (2 * n) := ⟨by omega⟩
      -- Map vertices of Bool × V into (false, 0, g) and (false, b, g - x b)
      let embV : Bool × V → Bool × B × V := fun z =>
        if z.1 then (false, b, z.2 - x b) else (false, 0, z.2)
      -- Map an edge of H (with endpoints z1, z2) to the unique midpoint (true, *, *)!
      let midOf : Bool × V → Bool × V → Bool × B × V := fun z1 z2 =>
        let gL := if z1.1 then z2.2 else z1.2
        let gR := if z1.1 then z1.2 else z2.2
        if gR = gL then (true, 0, gL)
        else if gR = gL + u then (true, b, gL + y 0)
        else (true, 2 • b, gL + x 0)
      have hmid_adj : ∀ z1 z2, H.Adj z1 z2 →
          (GNorm a b x y).Adj (embV z1) (midOf z1 z2) ∧
          (GNorm a b x y).Adj (midOf z1 z2) (embV z2) := by
        intro z1 z2 hadj
        have hba : b + a = 0 := by rw [ha2b]; linear_combination (norm := abel) h3b
        have hbb : b + b = 2 • b := by abel
        have orient : ∀ gL gR, (gR = gL ∨ gR = gL + u ∨ gR = gL + v) →
            (GNorm a b x y).Adj (false, 0, gL) (if gR = gL then (true, 0, gL)
              else if gR = gL + u then (true, b, gL + y 0) else (true, 2 • b, gL + x 0)) ∧
            (GNorm a b x y).Adj (if gR = gL then (true, 0, gL)
              else if gR = gL + u then (true, b, gL + y 0) else (true, 2 • b, gL + x 0))
              (false, b, gR - x b) := by
          intro gL gR h
          by_cases h1 : gR = gL
          · rw [h1]; simp only [↓reduceIte]
            exact ⟨e0 0 gL, by simpa [hba, sub_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) b (gL - x b)⟩
          · by_cases h2 : gR = gL + u
            · subst h2; simp only [h1, ↓reduceIte]
              have hv1 : gL + u - x b = gL + y 0 := by dsimp [u]; abel
              exact ⟨by simpa [zero_add] using eb (a := a) (b := b) (x := x) (y := y) 0 gL, by simpa [hv1] using e0' (a := a) (b := b) (x := x) (y := y) b (gL + y 0)⟩
            · have h3 : gR = gL + v := (h.resolve_left h1).resolve_left h2
              subst h3; simp only [h1, h2, ↓reduceIte]
              have hv2 : gL + v - x b + y b = gL + x 0 := by dsimp [v]; abel
              exact ⟨by simpa [ha2b, zero_add] using ea (a := a) (b := b) (x := x) (y := y) 0 gL,
                by simpa [hbb, hv2] using eb' (a := a) (b := b) (x := x) (y := y) b (gL + v - x b)⟩
        rcases hadj with ⟨_, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
        · have := orient z1.2 z2.2 h3
          simpa [embV, midOf, h1, h2] using this
        · have := orient z2.2 z1.2 h3
          simpa [embV, midOf, h1, h2] using And.intro this.2.symm this.1.symm
      -- Build the 2*n walk!
      let F : Fin (2 * n) → Bool × B × V := fun k =>
        let q : Fin n := ⟨k.val / 2, Nat.div_lt_of_lt_mul (by omega)⟩
        if k.val % 2 = 0 then embV (c q) else midOf (c q) (c (q + 1))
      -- Helper: c q is adjacent to c (q + 1) in H
      have hc_adj : ∀ q : Fin n, H.Adj (c q) (c (q + 1)) := by
        intro q
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        exact c.toHom.map_rel (by rw [SimpleGraph.cycleGraph_adj]; right; simp)
      apply walk_to_cycle (by omega) F
      · -- Injectivity of F!
        intro i j hij
        have hside : (F i).1 = (F j).1 := congrArg Prod.fst hij
        by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0
        · -- Both even: embV (c qi) = embV (c qj)
          have heq : embV (c ⟨i.val / 2, Nat.div_lt_of_lt_mul (by omega)⟩) =
              embV (c ⟨j.val / 2, Nat.div_lt_of_lt_mul (by omega)⟩) := by
            simpa [F, hi, hj] using hij
          have hemb_inj : Function.Injective embV := by
            rintro ⟨s1, g1⟩ ⟨s2, g2⟩ h
            cases s1 <;> cases s2 <;> simp only [embV, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
            · exact Prod.ext rfl h.2.2
            · exact False.elim (hb h.2.1.symm)
            · exact False.elim (hb h.2.1)
            · exact Prod.ext rfl (sub_left_inj.mp h.2.2)
          have hq := c.injective (hemb_inj heq)
          have hdiv : i.val / 2 = j.val / 2 := congrArg Fin.val hq
          exact Fin.ext (by omega)
        · -- Even vs odd: false vs true!
          have hf1 : (F i).1 = false := by
            simp only [F, hi, ↓reduceIte, embV]; cases (c _).1 <;> rfl
          have hf2 : (F j).1 = true := by
            simp only [F, hj, ↓reduceIte, midOf, apply_ite Prod.fst, ite_self]
          rw [hf1, hf2] at hside; cases hside
        · -- Odd vs even: true vs false!
          have hf1 : (F i).1 = true := by
            simp only [F, hi, ↓reduceIte, midOf, apply_ite Prod.fst, ite_self]
          have hf2 : (F j).1 = false := by
            simp only [F, hj, ↓reduceIte, embV]; cases (c _).1 <;> rfl
          rw [hf1, hf2] at hside; cases hside
        · -- Both odd: midOf (c qi) (c (qi+1)) = midOf (c qj) (c (qj+1))!
          let qi : Fin n := ⟨i.val / 2, Nat.div_lt_of_lt_mul (by omega)⟩
          let qj : Fin n := ⟨j.val / 2, Nat.div_lt_of_lt_mul (by omega)⟩
          have hm : midOf (c qi) (c (qi + 1)) = midOf (c qj) (c (qj + 1)) := by
            simpa [F, hi, hj] using hij
          -- Recover the unordered edge {c qi, c (qi+1)} = {c qj, c (qj+1)} from midOf!
          have hmid_edge : ∀ z1 z2 w1 w2, H.Adj z1 z2 → H.Adj w1 w2 →
              midOf z1 z2 = midOf w1 w2 → (z1 = w1 ∧ z2 = w2) ∨ (z1 = w2 ∧ z2 = w1) := by
            intro z1 z2 w1 w2 hz hw hm'
            -- Each H.Adj has one false and one true vertex; midOf determines both gL and the shift!
            have recover : ∀ gL1 gR1 gL2 gR2,
                (gR1 = gL1 ∨ gR1 = gL1 + u ∨ gR1 = gL1 + v) →
                (gR2 = gL2 ∨ gR2 = gL2 + u ∨ gR2 = gL2 + v) →
                (if gR1 = gL1 then ((true : Bool), (0 : B), gL1)
                 else if gR1 = gL1 + u then (true, b, gL1 + y 0) else (true, 2 • b, gL1 + x 0)) =
                (if gR2 = gL2 then (true, 0, gL2)
                 else if gR2 = gL2 + u then (true, b, gL2 + y 0) else (true, 2 • b, gL2 + x 0)) →
                gL1 = gL2 ∧ gR1 = gR2 := by
              intro gL1 gR1 gL2 gR2 h1 h2 heq
              have hB := congrArg (fun z : Bool × B × V => z.2.1) heq
              have hV := congrArg (fun z : Bool × B × V => z.2.2) heq
              by_cases c1 : gR1 = gL1 <;> by_cases c2 : gR2 = gL2
              · simp only [if_pos c1, if_pos c2] at hV
                exact ⟨hV, by rw [c1, c2, hV]⟩
              · by_cases c4 : gR2 = gL2 + u
                · simp only [if_pos c1, if_neg c2, if_pos c4] at hB; exact False.elim (hb hB.symm)
                · simp only [if_pos c1, if_neg c2, if_neg c4] at hB; exact False.elim (h2b hB.symm)
              · by_cases c3 : gR1 = gL1 + u
                · simp only [if_neg c1, if_pos c2, if_pos c3] at hB; exact False.elim (hb hB)
                · simp only [if_neg c1, if_pos c2, if_neg c3] at hB; exact False.elim (h2b hB)
              · by_cases c3 : gR1 = gL1 + u <;> by_cases c4 : gR2 = gL2 + u
                · simp only [if_neg c1, if_neg c2, if_pos c3, if_pos c4] at hV
                  have hL : gL1 = gL2 := add_right_cancel hV
                  exact ⟨hL, by rw [c3, c4, hL]⟩
                · simp only [if_neg c1, if_neg c2, if_pos c3, if_neg c4] at hB
                  exact False.elim (hb (by linear_combination (norm := abel) -hB))
                · simp only [if_neg c1, if_neg c2, if_neg c3, if_pos c4] at hB
                  exact False.elim (hb (by linear_combination (norm := abel) hB))
                · simp only [if_neg c1, if_neg c2, if_neg c3, if_neg c4] at hV
                  have hL : gL1 = gL2 := add_right_cancel hV
                  have hR1 : gR1 = gL1 + v := (h1.resolve_left c1).resolve_left c3
                  have hR2 : gR2 = gL2 + v := (h2.resolve_left c2).resolve_left c4
                  exact ⟨hL, by rw [hR1, hR2, hL]⟩
            rcases hz with ⟨_, ⟨hz1, hz2, hz3⟩ | ⟨hz1, hz2, hz3⟩⟩ <;>
            rcases hw with ⟨_, ⟨hw1, hw2, hw3⟩ | ⟨hw1, hw2, hw3⟩⟩
            · simp only [midOf, hz1, hw1, Bool.false_eq_true, ↓reduceIte] at hm'
              obtain ⟨hL, hR⟩ := recover _ _ _ _ hz3 hw3 hm'
              left; exact ⟨Prod.ext (hz1.trans hw1.symm) hL, Prod.ext (hz2.trans hw2.symm) hR⟩
            · simp only [midOf, hz1, hw2, Bool.false_eq_true, ↓reduceIte] at hm'
              obtain ⟨hL, hR⟩ := recover _ _ _ _ hz3 hw3 hm'
              right; exact ⟨Prod.ext (hz1.trans hw1.symm) hL, Prod.ext (hz2.trans hw2.symm) hR⟩
            · simp only [midOf, hz2, hw1, Bool.false_eq_true, ↓reduceIte] at hm'
              obtain ⟨hL, hR⟩ := recover _ _ _ _ hz3 hw3 hm'
              right; exact ⟨Prod.ext (hz2.trans hw2.symm) hR, Prod.ext (hz1.trans hw1.symm) hL⟩
            · simp only [midOf, hz2, hw2, Bool.false_eq_true, ↓reduceIte] at hm'
              obtain ⟨hL, hR⟩ := recover _ _ _ _ hz3 hw3 hm'
              left; exact ⟨Prod.ext (hz2.trans hw2.symm) hR, Prod.ext (hz1.trans hw1.symm) hL⟩
          rcases hmid_edge _ _ _ _ (hc_adj qi) (hc_adj qj) hm with ⟨h1, _⟩ | ⟨h1, h2⟩
          · have hq := c.injective h1
            have hdiv : i.val / 2 = j.val / 2 := congrArg Fin.val hq
            exact Fin.ext (by omega)
          · -- c qi = c (qj + 1) ∧ c (qi + 1) = c qj => qi = qj + 1 ∧ qi + 1 = qj => 2 = 0 in Fin n, impossible for n ≥ 4!
            have e1 : qi = qj + 1 := c.injective h1
            have e2 : qi + 1 = qj := c.injective h2
            have h1n : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
            have h1v : qi.val = (qj.val + 1) % n := by rw [e1, Fin.val_add, h1n]
            have h2v : (qi.val + 1) % n = qj.val := by rw [← e2, Fin.val_add, h1n]
            have hqi := qi.isLt; have hqj := qj.isLt
            by_cases h1 : qj.val + 1 = n <;> by_cases h2 : qi.val + 1 = n
            · rw [h1, Nat.mod_self] at h1v; omega
            · rw [h1, Nat.mod_self] at h1v; rw [Nat.mod_eq_of_lt (by omega)] at h2v; omega
            · rw [h2, Nat.mod_self] at h2v; rw [Nat.mod_eq_of_lt (by omega)] at h1v; omega
            · rw [Nat.mod_eq_of_lt (by omega)] at h1v h2v; omega
      · -- Adjacency of consecutive steps F k -> F (k + 1)!
        intro k
        have h12n : (1 : Fin (2 * n)).val = 1 := by simp [Nat.mod_eq_of_lt (show 1 < 2 * n by omega)]
        have h1n : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
        have hklt := k.isLt
        have hk1lt := (k + 1).isLt
        have hk1v : (k + 1).val = (k.val + 1) % (2 * n) := by rw [Fin.val_add, h12n]
        by_cases hk : k.val % 2 = 0
        · -- k = 2q, k + 1 = 2q + 1!
          have hk1 : (k + 1).val = k.val + 1 := by rw [hk1v, Nat.mod_eq_of_lt (by omega)]
          have hk1_odd : (k + 1).val % 2 ≠ 0 := by omega
          have hdiv : (k + 1).val / 2 = k.val / 2 := by omega
          simp only [F, hk, hk1_odd, ↓reduceIte]
          have hqeq : (⟨(k + 1).val / 2, Nat.div_lt_of_lt_mul (show (k + 1).val < 2 * n from hk1lt)⟩ : Fin n) =
              ⟨k.val / 2, Nat.div_lt_of_lt_mul (show k.val < 2 * n from hklt)⟩ := Fin.ext hdiv
          rw [hqeq]
          exact (hmid_adj _ _ (hc_adj _)).1
        · -- k = 2q + 1, k + 1 = 2(q + 1) (mod 2n)!
          have hk1_even : (k + 1).val % 2 = 0 := by
            rw [hk1v]
            by_cases hlast : k.val + 1 = 2 * n
            · rw [hlast, Nat.mod_self]
            · have hlt : k.val + 1 < 2 * n := by omega
              rw [Nat.mod_eq_of_lt hlt]
              omega
          have hdiv : (⟨(k + 1).val / 2, Nat.div_lt_of_lt_mul (show (k + 1).val < 2 * n from hk1lt)⟩ : Fin n) =
              ⟨k.val / 2, Nat.div_lt_of_lt_mul (show k.val < 2 * n from hklt)⟩ + 1 := by
            apply Fin.ext
            change (k + 1).val / 2 = (k.val / 2 + (1 : Fin n).val) % n
            rw [hk1v, h1n]
            by_cases hlast : k.val + 1 = 2 * n
            · rw [hlast, Nat.mod_self, Nat.zero_div]
              have h2 : k.val / 2 + 1 = n := by omega
              rw [h2, Nat.mod_self]
            · have hlt1 : k.val + 1 < 2 * n := by omega
              have hlt2 : k.val / 2 + 1 < n := by omega
              rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]; omega
          simp only [F, hk, hk1_even, ↓reduceIte]
          rw [hdiv]
          exact (hmid_adj _ _ (hc_adj _)).2
    rcases hshort with h4 | h8 | h16
    · exact hasPow2_of_8 (subdiv (by decide) h4)
    · exact hasPow2_of_16 (subdiv (by decide) h8)
    · exact hasPow2_of_32 (subdiv (by decide) h16)

/-- Subcase 2b: `a = 2 • b` and `5 • b = 0` (`B ≅ ℤ/5`): proved by 8 simple 4/8-cycles and
5 shifts of 1 edge-neutral 16-cycle! -/
lemma case_a2b_z5 (hb : b ≠ 0) (ha2b : a = 2 • b) (h5b : 5 • b = 0) :
    HasPow2 (GNorm a b x y) := by
  by_contra hno
  -- The 5 elements 0, b, 2b, 3b, 4b are pairwise distinct!
  have h2b : 2 • b ≠ 0 := by
    intro e; exact hb (by linear_combination (norm := abel) h5b - 2 • e)
  have h3b : 3 • b ≠ 0 := by
    intro e; exact h2b (by linear_combination (norm := abel) h5b - e)
  have h4b : 4 • b ≠ 0 := by
    intro e; exact hb (by linear_combination (norm := abel) h5b - e)
  let ptB : ZMod 5 → B := fun k => k.val • b
  have hptB_add : ∀ k : ZMod 5, ptB (k + 1) = ptB k + b := by
    intro k; fin_cases k <;> dsimp [ptB]
    · change (1 : ℕ) • b = (0 : ℕ) • b + b; abel
    · change (2 : ℕ) • b = (1 : ℕ) • b + b; abel
    · change (3 : ℕ) • b = (2 : ℕ) • b + b; abel
    · change (4 : ℕ) • b = (3 : ℕ) • b + b; abel
    · change (0 : ℕ) • b = (4 : ℕ) • b + b; linear_combination (norm := abel) -h5b
  have hptB_add2 : ∀ k : ZMod 5, ptB (k + 2) = ptB k + a := by
    intro k; rw [ha2b, show k + 2 = (k + 1) + 1 from by ring, hptB_add, hptB_add]; abel
  have hptB_inj : Function.Injective ptB := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [ptB, ZMod.val, Fin.val] at hij
    all_goals first
      | rfl
      | (solve | exfalso; apply hb; linear_combination (norm := abel) hij)
      | (solve | exfalso; apply hb; linear_combination (norm := abel) -hij)
      | (solve | exfalso; apply h2b; linear_combination (norm := abel) hij)
      | (solve | exfalso; apply h2b; linear_combination (norm := abel) -hij)
      | (solve | exfalso; apply h3b; linear_combination (norm := abel) hij)
      | (solve | exfalso; apply h3b; linear_combination (norm := abel) -hij)
      | (solve | exfalso; apply h4b; linear_combination (norm := abel) hij)
      | (solve | exfalso; apply h4b; linear_combination (norm := abel) -hij)
  -- Define q k := q2V b x y (ptB k) and S := ∑ k : ZMod 5, y (ptB k)!
  let q : ZMod 5 → V := fun k => y (ptB k) + y (ptB (k + 1)) - x (ptB k)
  let S : V := y (ptB 0) + y (ptB 1) + y (ptB 2) + y (ptB 3) + y (ptB 4)
  -- Helper: any 4-cycle Q(k) has voltage q k, so q k ≠ 0!
  have hq_nz : ∀ k : ZMod 5, q k ≠ 0 := fun k hq =>
    hno (case_a2b_c4 hb ha2b h2b (ptB k) (by simpa [q2V, q, hptB_add] using hq))
  -- Helper for simple 8-cycles on ZMod 5:
  have mk8 : ∀ (w : Fin 8 → Bool × ZMod 5) (gv : Fin 8 → V),
      Function.Injective w →
      (∀ i : Fin 8, (GNorm a b x y).Adj
        ((w i).1, ptB (w i).2, gv i) ((w (i + 1)).1, ptB (w (i + 1)).2, gv (i + 1))) →
      False := by
    intro w gv hw hstep
    apply hno; apply hasPow2_of_8
    refine walk_to_cycle (by decide) (fun i => ((w i).1, ptB (w i).2, gv i)) ?_ hstep
    intro i j hij
    exact hw (Prod.ext (congrArg (fun z : Bool × B × V => z.1) hij) (hptB_inj (congrArg (fun z : Bool × B × V => z.2.1) hij)))
  -- The 7 simple 8-cycle inequalities (verified in Python!):
  -- 1. q 0 - q 1 + q 2 ≠ 0  (and shifted by 1: q 1 - q 2 + q 3 ≠ 0!)
  have hc8_A : ∀ k : ZMod 5, q k - q (k + 1) + q (k + 2) ≠ 0 := by
    intro k h0
    let w : Fin 8 → Bool × ZMod 5 := ![
      (false, k), (true, k + 1), (false, k + 1), (true, k + 3),
      (false, k + 3), (true, k + 4), (false, k + 2), (true, k + 2)]
    let gv : Fin 8 → V := ![
      0, y (ptB k), y (ptB k), y (ptB k) + x (ptB (k + 1)),
      y (ptB k) + x (ptB (k + 1)), y (ptB k) + x (ptB (k + 1)) + y (ptB (k + 3)),
      y (ptB k) + x (ptB (k + 1)) + y (ptB (k + 3)) - x (ptB (k + 2)),
      y (ptB k) + x (ptB (k + 1)) + y (ptB (k + 3)) - x (ptB (k + 2))]
    apply mk8 w gv (by clear h0; revert k; decide)
    · intro i; fin_cases i <;> dsimp [w, gv]
      · simpa [hptB_add] using eb (a := a) (b := b) (x := x) (y := y) (ptB k) 0
      · exact e0' (ptB (k + 1)) _
      · rw [show k + 3 = (k + 1) + 2 by ring, hptB_add2]; exact ea (ptB (k + 1)) _
      · exact e0' (ptB (k + 3)) _
      · have h := eb (a := a) (b := b) (x := x) (y := y) (ptB (k + 3)) (y (ptB k) + x (ptB (k + 1))); rwa [← hptB_add, show k + 3 + 1 = k + 4 by ring] at h
      · rw [show k + 4 = (k + 2) + 2 by ring, hptB_add2]; exact ea_sub (ptB (k + 2)) _
      · exact e0 (ptB (k + 2)) _
      · have hv : 0 + x (ptB k) = y (ptB k) + x (ptB (k + 1)) + y (ptB (k + 3)) - x (ptB (k + 2)) := by
          dsimp [q] at h0
          rw [show k + 1 + 1 = k + 2 by ring, show k + 2 + 1 = k + 3 by ring] at h0
          linear_combination (norm := abel) -h0
        have h := ea' (a := a) (b := b) (x := x) (y := y) (ptB k) 0
        rwa [← hptB_add2, hv] at h
  -- 2. q 2 - S ≠ 0: walk (0,0)-(1,0)-(0,4)-(1,4)-(0,2)-(1,2)-(0,1)-(1,1)
  --    Voltage: -y4 - x2 - y1 + x0? Let's check:
  --    (0,0)-0->(1,0)-b'->(0,4)-0->(1,4)-a'->(0,2)-0->(1,2)-b'->(0,1)-0->(1,1)-b'->(0,0)!
  --    Voltage = -y4 - x2 - y1 - y0 = -(y0+y1+y4+x2) = q 2 - S!
  have hc8_B : q 2 - S ≠ 0 := by
    intro h0
    let w : Fin 8 → Bool × ZMod 5 := ![
      (false, 0), (true, 0), (false, 4), (true, 4),
      (false, 2), (true, 2), (false, 1), (true, 1)]
    let gv : Fin 8 → V := ![
      0, 0, -y (ptB 4), -y (ptB 4),
      -y (ptB 4) - x (ptB 2), -y (ptB 4) - x (ptB 2),
      -y (ptB 4) - x (ptB 2) - y (ptB 1), -y (ptB 4) - x (ptB 2) - y (ptB 1)]
    apply mk8 w gv (by decide)
    intro i; fin_cases i <;> dsimp [w, gv]
    · exact e0 (ptB 0) 0
    · rw [show (0 : ZMod 5) = 4 + 1 by decide, hptB_add]; simpa [zero_sub] using eb_sub (a := a) (b := b) (x := x) (y := y) (ptB 4) 0
    · exact e0 (ptB 4) _
    · rw [show (4 : ZMod 5) = 2 + 2 by decide, hptB_add2]; exact ea_sub (ptB 2) _
    · exact e0 (ptB 2) _
    · rw [show (2 : ZMod 5) = 1 + 1 by decide, hptB_add]; exact eb_sub (ptB 1) _
    · exact e0 (ptB 1) _
    · have hv : 0 + y (ptB 0) = -y (ptB 4) - x (ptB 2) - y (ptB 1) := by
        dsimp [q, S] at h0; rw [show (2 : ZMod 5) + 1 = 3 by decide] at h0
        linear_combination (norm := abel) -h0
      have h := eb' (a := a) (b := b) (x := x) (y := y) (ptB 0) 0
      rwa [← hptB_add, show (0 : ZMod 5) + 1 = 1 by decide, hv] at h
  -- 3. q 1 + q 2 - S ≠ 0: walk (0,0)-(1,0)-(0,4)-(1,4)-(0,2)-(1,3)-(0,1)-(1,1)
  have hc8_C : q 1 + q 2 - S ≠ 0 := by
    intro h0
    let w : Fin 8 → Bool × ZMod 5 := ![
      (false, 0), (true, 0), (false, 4), (true, 4),
      (false, 2), (true, 3), (false, 1), (true, 1)]
    let gv : Fin 8 → V := ![
      0, 0, -y (ptB 4), -y (ptB 4),
      -y (ptB 4) - x (ptB 2), -y (ptB 4) - x (ptB 2) + y (ptB 2),
      -y (ptB 4) - x (ptB 2) + y (ptB 2) - x (ptB 1),
      -y (ptB 4) - x (ptB 2) + y (ptB 2) - x (ptB 1)]
    apply mk8 w gv (by decide)
    intro i; fin_cases i <;> dsimp [w, gv]
    · exact e0 (ptB 0) 0
    · rw [show (0 : ZMod 5) = 4 + 1 by decide, hptB_add]; simpa [zero_sub] using eb_sub (a := a) (b := b) (x := x) (y := y) (ptB 4) 0
    · exact e0 (ptB 4) _
    · rw [show (4 : ZMod 5) = 2 + 2 by decide, hptB_add2]; exact ea_sub (ptB 2) _
    · rw [show (3 : ZMod 5) = 2 + 1 by decide, hptB_add]; exact eb (ptB 2) _
    · rw [show (3 : ZMod 5) = 1 + 2 by decide, hptB_add2]; exact ea_sub (ptB 1) _
    · exact e0 (ptB 1) _
    · have hv : 0 + y (ptB 0) = -y (ptB 4) - x (ptB 2) + y (ptB 2) - x (ptB 1) := by
        dsimp [q, S] at h0
        rw [show (1 : ZMod 5) + 1 = 2 by decide, show (2 : ZMod 5) + 1 = 3 by decide] at h0
        linear_combination (norm := abel) -h0
      have h := eb' (a := a) (b := b) (x := x) (y := y) (ptB 0) 0
      rwa [← hptB_add, show (0 : ZMod 5) + 1 = 1 by decide, hv] at h
  -- 4. q 0 - q 1 - q 4 ≠ 0: walk (0,0)-(1,0)-(0,4)-(1,1)-(0,1)-(1,3)-(0,2)-(1,2)
  have hc8_D : q 0 - q 1 - q 4 ≠ 0 := by
    intro h0
    let w : Fin 8 → Bool × ZMod 5 := ![
      (false, 0), (true, 0), (false, 4), (true, 1),
      (false, 1), (true, 3), (false, 2), (true, 2)]
    let gv : Fin 8 → V := ![
      0, 0, -y (ptB 4), -y (ptB 4) + x (ptB 4),
      -y (ptB 4) + x (ptB 4), -y (ptB 4) + x (ptB 4) + x (ptB 1),
      -y (ptB 4) + x (ptB 4) + x (ptB 1) - y (ptB 2),
      -y (ptB 4) + x (ptB 4) + x (ptB 1) - y (ptB 2)]
    apply mk8 w gv (by decide)
    intro i; fin_cases i <;> dsimp [w, gv]
    · exact e0 (ptB 0) 0
    · rw [show (0 : ZMod 5) = 4 + 1 by decide, hptB_add]; simpa [zero_sub] using eb_sub (a := a) (b := b) (x := x) (y := y) (ptB 4) 0
    · rw [show (1 : ZMod 5) = 4 + 2 by decide, hptB_add2]; exact ea (ptB 4) _
    · exact e0' (ptB 1) _
    · rw [show (3 : ZMod 5) = 1 + 2 by decide, hptB_add2]; exact ea (ptB 1) _
    · rw [show (3 : ZMod 5) = 2 + 1 by decide, hptB_add]; exact eb_sub (ptB 2) _
    · exact e0 (ptB 2) _
    · have hv : 0 + x (ptB 0) = -y (ptB 4) + x (ptB 4) + x (ptB 1) - y (ptB 2) := by
        dsimp [q] at h0
        rw [show (0 : ZMod 5) + 1 = 1 by decide, show (1 : ZMod 5) + 1 = 2 by decide,
            show (4 : ZMod 5) + 1 = 0 by decide] at h0
        linear_combination (norm := abel) -h0
      have h := ea' (a := a) (b := b) (x := x) (y := y) (ptB 0) 0
      rwa [← hptB_add2, show (0 : ZMod 5) + 2 = 2 by decide, hv] at h
  -- 5. q 0 + q 3 - q 4 ≠ 0: walk (0,0)-(1,0)-(0,3)-(1,4)-(0,4)-(1,1)-(0,1)-(1,2)
  have hc8_E : q 0 + q 3 - q 4 ≠ 0 := by
    intro h0
    let w : Fin 8 → Bool × ZMod 5 := ![
      (false, 0), (true, 0), (false, 3), (true, 4),
      (false, 4), (true, 1), (false, 1), (true, 2)]
    let gv : Fin 8 → V := ![
      0, 0, -x (ptB 3), -x (ptB 3) + y (ptB 3),
      -x (ptB 3) + y (ptB 3), -x (ptB 3) + y (ptB 3) + x (ptB 4),
      -x (ptB 3) + y (ptB 3) + x (ptB 4), -x (ptB 3) + y (ptB 3) + x (ptB 4) + y (ptB 1)]
    apply mk8 w gv (by decide)
    intro i; fin_cases i <;> dsimp [w, gv]
    · exact e0 (ptB 0) 0
    · rw [show (0 : ZMod 5) = 3 + 2 by decide, hptB_add2]; simpa [zero_sub] using ea_sub (a := a) (b := b) (x := x) (y := y) (ptB 3) 0
    · rw [show (4 : ZMod 5) = 3 + 1 by decide, hptB_add]; exact eb (ptB 3) _
    · exact e0' (ptB 4) _
    · rw [show (1 : ZMod 5) = 4 + 2 by decide, hptB_add2]; exact ea (ptB 4) _
    · exact e0' (ptB 1) _
    · rw [show (2 : ZMod 5) = 1 + 1 by decide, hptB_add]; exact eb (ptB 1) _
    · rw [show (2 : ZMod 5) = 0 + 2 by decide, hptB_add2]
      have hv : 0 + x (ptB 0) = -x (ptB 3) + y (ptB 3) + x (ptB 4) + y (ptB 1) := by
        dsimp [q] at h0
        rw [show (0 : ZMod 5) + 1 = 1 by decide, show (3 : ZMod 5) + 1 = 4 by decide,
            show (4 : ZMod 5) + 1 = 0 by decide] at h0
        linear_combination (norm := abel) -h0
      simpa [hv] using ea' (a := a) (b := b) (x := x) (y := y) (ptB 0) 0
  -- 6. q 0 + q 1 + q 4 - S ≠ 0: walk (0,0)-(1,1)-(0,4)-(1,4)-(0,3)-(1,3)-(0,1)-(1,2)
  have hc8_F : q 0 + q 1 + q 4 - S ≠ 0 := by
    intro h0
    let w : Fin 8 → Bool × ZMod 5 := ![
      (false, 0), (true, 1), (false, 4), (true, 4),
      (false, 3), (true, 3), (false, 1), (true, 2)]
    let gv : Fin 8 → V := ![
      0, y (ptB 0), y (ptB 0) - x (ptB 4), y (ptB 0) - x (ptB 4),
      y (ptB 0) - x (ptB 4) - y (ptB 3), y (ptB 0) - x (ptB 4) - y (ptB 3),
      y (ptB 0) - x (ptB 4) - y (ptB 3) - x (ptB 1),
      y (ptB 0) - x (ptB 4) - y (ptB 3) - x (ptB 1) + y (ptB 1)]
    apply mk8 w gv (by decide)
    intro i; fin_cases i <;> dsimp [w, gv]
    · rw [show (1 : ZMod 5) = 0 + 1 by decide, hptB_add]; simpa using eb (a := a) (b := b) (x := x) (y := y) (ptB 0) 0
    · rw [show (1 : ZMod 5) = 4 + 2 by decide, hptB_add2]; exact ea_sub (ptB 4) _
    · exact e0 (ptB 4) _
    · rw [show (4 : ZMod 5) = 3 + 1 by decide, hptB_add]; exact eb_sub (ptB 3) _
    · exact e0 (ptB 3) _
    · rw [show (3 : ZMod 5) = 1 + 2 by decide, hptB_add2]; exact ea_sub (ptB 1) _
    · rw [show (2 : ZMod 5) = 1 + 1 by decide, hptB_add]; exact eb (ptB 1) _
    · rw [show (2 : ZMod 5) = 0 + 2 by decide, hptB_add2]
      have hv : 0 + x (ptB 0) = y (ptB 0) - x (ptB 4) - y (ptB 3) - x (ptB 1) + y (ptB 1) := by
        dsimp [q, S] at h0
        rw [show (0 : ZMod 5) + 1 = 1 by decide, show (1 : ZMod 5) + 1 = 2 by decide,
            show (4 : ZMod 5) + 1 = 0 by decide] at h0
        linear_combination (norm := abel) -h0
      simpa [hv] using ea' (a := a) (b := b) (x := x) (y := y) (ptB 0) 0
  -- The edge-neutral 16-cycle shifted by any k : ZMod 5!
  -- Walk at shift k: (0,k),(1,k),(0,k+4),(1,k+4),(0,k+3),(1,k),(0,k),(1,k+2),(0,k+2),(1,k+4),(0,k+4),(1,k),(0,k+3),(1,k+4),(0,k+2),(1,k+2)
  -- Gives: S - q k - q (k + 2) = 0  ∨  S - q k - q (k + 2) - q (k + 3) = 0!
  have hc16 : ∀ k : ZMod 5, S - q k - q (k + 2) = 0 ∨ S - q k - q (k + 2) - q (k + 3) = 0 := by
    intro k
    by_contra hboth
    push_neg at hboth
    have hq3 : q (k + 3) ≠ 0 := hq_nz (k + 3)
    let w : Fin 16 → Bool × ZMod 5 := ![
      (false, k), (true, k), (false, k + 4), (true, k + 4),
      (false, k + 3), (true, k), (false, k), (true, k + 2),
      (false, k + 2), (true, k + 4), (false, k + 4), (true, k),
      (false, k + 3), (true, k + 4), (false, k + 2), (true, k + 2)]
    let g0 : V := 0
    let g1 : V := 0
    let g2 : V := -y (ptB (k + 4))
    let g3 : V := -y (ptB (k + 4))
    let g4 : V := -y (ptB (k + 4)) - y (ptB (k + 3))
    let g5 : V := -y (ptB (k + 4)) - y (ptB (k + 3)) + x (ptB (k + 3))
    let g6 : V := -y (ptB (k + 4)) - y (ptB (k + 3)) + x (ptB (k + 3))
    let g7 : V := -y (ptB (k + 4)) - y (ptB (k + 3)) + x (ptB (k + 3)) + x (ptB k)
    let g8 : V := -y (ptB (k + 4)) - y (ptB (k + 3)) + x (ptB (k + 3)) + x (ptB k)
    let g9 : V := -y (ptB (k + 4)) - y (ptB (k + 3)) + x (ptB (k + 3)) + x (ptB k) + x (ptB (k + 2))
    let g10 : V := -y (ptB (k + 4)) - y (ptB (k + 3)) + x (ptB (k + 3)) + x (ptB k) + x (ptB (k + 2))
    let g11 : V := -y (ptB (k + 3)) + x (ptB (k + 3)) + x (ptB k) + x (ptB (k + 2))
    let g12 : V := -y (ptB (k + 3)) + x (ptB k) + x (ptB (k + 2))
    let g13 : V := x (ptB k) + x (ptB (k + 2))
    let g14 : V := x (ptB k)
    let g15 : V := x (ptB k)
    let gv : Fin 16 → V := ![g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    -- Check the 3 voltage differences at repeated vertices!
    have hS_k : S = y (ptB k) + y (ptB (k + 1)) + y (ptB (k + 2)) + y (ptB (k + 3)) + y (ptB (k + 4)) := by
      have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by clear hboth hq3; revert k; decide
      rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> dsimp [S]
      · simp only [show (0 : ZMod 5) + 1 = 1 by decide, show (0 : ZMod 5) + 2 = 2 by decide, show (0 : ZMod 5) + 3 = 3 by decide, show (0 : ZMod 5) + 4 = 4 by decide]
      · simp only [show (1 : ZMod 5) + 1 = 2 by decide, show (1 : ZMod 5) + 2 = 3 by decide, show (1 : ZMod 5) + 3 = 4 by decide, show (1 : ZMod 5) + 4 = 0 by decide]; abel
      · simp only [show (2 : ZMod 5) + 1 = 3 by decide, show (2 : ZMod 5) + 2 = 4 by decide, show (2 : ZMod 5) + 3 = 0 by decide, show (2 : ZMod 5) + 4 = 1 by decide]; abel
      · simp only [show (3 : ZMod 5) + 1 = 4 by decide, show (3 : ZMod 5) + 2 = 0 by decide, show (3 : ZMod 5) + 3 = 1 by decide, show (3 : ZMod 5) + 4 = 2 by decide]; abel
      · simp only [show (4 : ZMod 5) + 1 = 0 by decide, show (4 : ZMod 5) + 2 = 1 by decide, show (4 : ZMod 5) + 3 = 2 by decide, show (4 : ZMod 5) + 4 = 3 by decide]; abel
    have h_d1 : g6 - g0 = -q (k + 3) := by
      dsimp [g6, g0, q]; rw [show k + 3 + 1 = k + 4 by ring]; abel
    have h_d2 : g11 - g1 = S - q k - q (k + 2) - q (k + 3) := by
      dsimp [g11, g1, q]
      rw [hS_k, show k + 2 + 1 = k + 3 by ring, show k + 3 + 1 = k + 4 by ring]; abel
    have h_d3 : g11 - g5 = S - q k - q (k + 2) := by
      dsimp [g11, g5, q]
      rw [hS_k, show k + 2 + 1 = k + 3 by ring]; abel
    have h_d4 : g10 - g2 = S - q k - q (k + 2) - q (k + 3) := by
      dsimp [g10, g2, q]
      rw [hS_k, show k + 2 + 1 = k + 3 by ring, show k + 3 + 1 = k + 4 by ring]; abel
    have h_d5 : g13 - g3 = S - q k - q (k + 2) := by
      dsimp [g13, g3, q]
      rw [hS_k, show k + 2 + 1 = k + 3 by ring]; abel
    have h_d6 : g13 - g9 = q (k + 3) := by
      dsimp [g13, g9, q]; rw [show k + 3 + 1 = k + 4 by ring]; abel
    have h_d7 : g12 - g4 = S - q k - q (k + 2) := by
      dsimp [g12, g4, q]
      rw [hS_k, show k + 2 + 1 = k + 3 by ring]; abel
    have h_d8 : g14 - g8 = q (k + 3) := by
      dsimp [g14, g8, q]; rw [show k + 3 + 1 = k + 4 by ring]; abel
    let w0 : Fin 16 → Bool × ZMod 5 := ![
      (false, 0), (true, 0), (false, 4), (true, 4),
      (false, 3), (true, 0), (false, 0), (true, 2),
      (false, 2), (true, 4), (false, 4), (true, 0),
      (false, 3), (true, 4), (false, 2), (true, 2)]
    have hw_eq : ∀ i : Fin 16, w i = ((w0 i).1, k + (w0 i).2) := by
      intro i; fin_cases i <;> dsimp [w, w0] <;> simp
    have hu_inj : Function.Injective (fun z : Bool × ZMod 5 => (z.1, ptB (k + z.2))) := by
      rintro ⟨s1, z1⟩ ⟨s2, z2⟩ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (add_left_cancel (hptB_inj h.2))
    apply hno; apply hasPow2_of_16
    refine walk_to_cycle (by decide) (fun i => ((w i).1, ptB (w i).2, gv i)) ?_ ?_
    · have hf_eq : (fun i => ((w i).1, ptB (w i).2, gv i)) = (fun i => ((w0 i).1, ptB (k + (w0 i).2), gv i)) := by
        funext i; rw [hw_eq i]
      rw [hf_eq]
      refine walk_inj_of_cols (fun z : Bool × ZMod 5 => (z.1, ptB (k + z.2))) hu_inj w0 gv
        [(0, 6), (1, 5), (1, 11), (5, 11), (2, 10), (3, 9), (3, 13), (9, 13), (4, 12), (7, 15), (8, 14)]
        (by decide) ?_
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp [gv] <;> intro hg
      · apply hq3; linear_combination (norm := abel) h_d1 + hg
      · apply hq3; dsimp [g5, g1, q] at hg ⊢; rw [show k + 3 + 1 = k + 4 by ring]; linear_combination (norm := abel) hg
      · apply hboth.2; linear_combination (norm := abel) -h_d2 - hg
      · apply hboth.1; linear_combination (norm := abel) -h_d3 - hg
      · apply hboth.2; linear_combination (norm := abel) -h_d4 - hg
      · apply hboth.2; dsimp [g9, g3, q] at hg ⊢; rw [hS_k, show k + 2 + 1 = k + 3 by ring, show k + 3 + 1 = k + 4 by ring]; linear_combination (norm := abel) -hg
      · apply hboth.1; linear_combination (norm := abel) -h_d5 - hg
      · apply hq3; linear_combination (norm := abel) -h_d6 - hg
      · apply hboth.1; linear_combination (norm := abel) -h_d7 - hg
      · apply hq3; dsimp [g15, g7, q] at hg ⊢; rw [show k + 3 + 1 = k + 4 by ring]; linear_combination (norm := abel) -hg
      · apply hq3; linear_combination (norm := abel) -h_d8 - hg
    · intro i; fin_cases i <;> dsimp [w, gv]
      · exact e0 (ptB k) g0
      · have h := eb_sub (a := a) (b := b) (x := x) (y := y) (ptB (k + 4)) 0
        rw [← hptB_add, show k + 4 + 1 = k by rw [add_assoc, show (4 : ZMod 5) + 1 = 0 by decide, add_zero], zero_sub] at h; exact h
      · exact e0 (ptB (k + 4)) g2
      · have h := eb_sub (a := a) (b := b) (x := x) (y := y) (ptB (k + 3)) g3
        rw [← hptB_add, show k + 3 + 1 = k + 4 by ring] at h; exact h
      · have h := ea (a := a) (b := b) (x := x) (y := y) (ptB (k + 3)) g4
        rw [← hptB_add2, show k + 3 + 2 = k by rw [add_assoc, show (3 : ZMod 5) + 2 = 0 by decide, add_zero]] at h; exact h
      · exact e0' (ptB k) g5
      · have h := ea (a := a) (b := b) (x := x) (y := y) (ptB k) g6
        rw [← hptB_add2] at h; exact h
      · exact e0' (ptB (k + 2)) g7
      · have h := ea (a := a) (b := b) (x := x) (y := y) (ptB (k + 2)) g8
        rw [← hptB_add2, show k + 2 + 2 = k + 4 by ring] at h; exact h
      · exact e0' (ptB (k + 4)) g9
      · have hv : g10 + y (ptB (k + 4)) = g11 := by dsimp [g10, g11]; abel
        have h := eb (a := a) (b := b) (x := x) (y := y) (ptB (k + 4)) g10
        rw [← hptB_add, show k + 4 + 1 = k by rw [add_assoc, show (4 : ZMod 5) + 1 = 0 by decide, add_zero], hv] at h; exact h
      · have hv : g12 + x (ptB (k + 3)) = g11 := by dsimp [g12, g11]; abel
        have h := ea' (a := a) (b := b) (x := x) (y := y) (ptB (k + 3)) g12
        rw [← hptB_add2, show k + 3 + 2 = k by rw [add_assoc, show (3 : ZMod 5) + 2 = 0 by decide, add_zero], hv] at h; exact h
      · have hv : g12 + y (ptB (k + 3)) = g13 := by dsimp [g12, g13]; abel
        have h := eb (a := a) (b := b) (x := x) (y := y) (ptB (k + 3)) g12
        rw [← hptB_add, show k + 3 + 1 = k + 4 by ring, hv] at h; exact h
      · have hv : g14 + x (ptB (k + 2)) = g13 := rfl
        have h := ea' (a := a) (b := b) (x := x) (y := y) (ptB (k + 2)) g14
        rw [← hptB_add2, show k + 2 + 2 = k + 4 by ring, hv] at h; exact h
      · exact e0 (ptB (k + 2)) g14
      · have h := ea' (a := a) (b := b) (x := x) (y := y) (ptB k) 0
        rw [← hptB_add2, zero_add] at h; exact h
  -- Combine the 5 shifts of hc16 with the 7 8-cycles and 5 4-cycles!
  have c0 := hc16 0; have c1 := hc16 1; have c2 := hc16 2; have c3 := hc16 3; have c4 := hc16 4
  have hA0 := hc8_A 0; have hA1 := hc8_A 1
  simp only [show (0 : ZMod 5) + 1 = 1 by decide, show (0 : ZMod 5) + 2 = 2 by decide,
    show (0 : ZMod 5) + 3 = 3 by decide, show (1 : ZMod 5) + 1 = 2 by decide,
    show (1 : ZMod 5) + 2 = 3 by decide, show (1 : ZMod 5) + 3 = 4 by decide,
    show (2 : ZMod 5) + 2 = 4 by decide, show (2 : ZMod 5) + 3 = 0 by decide,
    show (3 : ZMod 5) + 2 = 0 by decide, show (3 : ZMod 5) + 3 = 1 by decide,
    show (4 : ZMod 5) + 2 = 1 by decide, show (4 : ZMod 5) + 3 = 2 by decide] at c0 c1 c2 c3 c4 hA0 hA1
  have hq0 := hq_nz 0; have hq1 := hq_nz 1; have hq2 := hq_nz 2; have hq3 := hq_nz 3; have hq4 := hq_nz 4
  rcases c0 with h0 | h0
  · rcases c2 with h2 | h2
    · rcases c3 with h3 | h3
      · rcases c1 with h1 | h1
        · exact hc8_C (by linear_combination (norm := abel) -h0 + h3 - h1)
        · exact hq1 (by linear_combination (norm := abel) h2 + h3 - h0 - h1)
      · exact hA1 (by linear_combination (norm := abel) h0 - h3)
    · exact hq4 (by linear_combination (norm := abel) h0 - h2)
  · rcases c3 with h3 | h3
    · exact hq2 (by linear_combination (norm := abel) h3 - h0)
    · rcases c1 with h1 | h1
      · exact hq0 (by linear_combination (norm := abel) h1 - h3)
      · rcases c4 with h4 | h4
        · exact hq3 (by linear_combination (norm := abel) h4 - h1)
        · rcases c2 with h2 | h2
          · exact hq1 (by linear_combination (norm := abel) h2 - h4)
          · exact hc8_F (by linear_combination (norm := abel) -h2 - h3 + h0)

/-- Subcase 2c: `a = 2 • b` with `0, b, 2b, 3b, 4b, 5b, 6b` distinct (`ord(b) ≥ 7`):
ONE single `(4, 4, 4)` Barbell between `Q(0)` and `Q(4b)`! -/
lemma case_a2b_ge7 (hb : b ≠ 0) (ha2b : a = 2 • b)
    (h2b : 2 • b ≠ 0) (h3b : 3 • b ≠ 0) (h4b : 4 • b ≠ 0) (h5b : 5 • b ≠ 0) (h6b : 6 • b ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  by_contra hno
  have hq0 : q2V b x y 0 ≠ 0 := fun h => hno (case_a2b_c4 hb ha2b h2b 0 h)
  have hq4 : q2V b x y (4 • b) ≠ 0 := fun h => hno (case_a2b_c4 hb ha2b h2b (4 • b) h)
  -- C1 = Q(0) starting at (true, 2b):
  --   0:(true,2b) --a'-> 1:(false,0) --b-> 2:(true,b) --0'-> 3:(false,b) --b-> (0, +q2V 0)
  -- Bar (len 4) from (true, 2b) to (false, 4b):
  --   0:(true,2b) --0'-> 4:(false,2b) --b-> 5:(true,3b) --0'-> 6:(false,3b) --b-> (true,4b)?
  --   Wait: 4-step path from (true, 2b) to (true, 4b):
  --   0:(true,2b) --0'-> 4:(false,2b) --b-> 5:(true,3b) --0'-> 6:(false,3b) --b-> 7:(true,4b) -> wait (true,4b) is NOT in Q(4b)!
  --   Check Q(4b) vertices: (false,4b), (true,5b), (false,5b), (true,6b)!
  --   Bar of len 4 from (true, 2b) to (true, 5b):
  --   0:(true,2b) --0'-> 4:(false,2b) --b-> 5:(true,3b) --0'-> 6:(false,3b) --a-> 7:(true,5b)!!
  --   CHECK!! (false,3b) + a = (true, 5b) ∈ Q(4b)!!
  -- C2 = Q(4b) starting at (true, 5b):
  --   7:(true,5b) --0'-> 8:(false,5b) --b-> 9:(true,6b) --a'-> 10:(false,4b) --b-> (7, +q2V(4b))!
  let u : Fin 11 → Bool × B := ![
    (true, 2 • b), (false, 0), (true, b), (false, b),
    (false, 2 • b), (true, 3 • b), (false, 3 • b),
    (true, 5 • b), (false, 5 • b), (true, 6 • b), (false, 4 • b)]
  have hu : Function.Injective u := by
    intro p r hpr
    fin_cases p <;> fin_cases r <;> dsimp [u] at hpr
    all_goals first
      | rfl
      | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
      | (have e := congrArg Prod.snd hpr; dsimp at e
         first | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
               | (solve | exfalso; apply hb; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h2b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h2b; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h3b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h3b; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h4b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h4b; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h5b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h5b; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h6b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h6b; linear_combination (norm := abel) -e))
  let g : Fin 11 → V := ![
    0, -x 0, -x 0 + y 0, -x 0 + y 0,
    0, y (2 • b), y (2 • b),
    y (2 • b) + x (3 • b), y (2 • b) + x (3 • b),
    y (2 • b) + x (3 • b) + y (5 • b),
    y (2 • b) + x (3 • b) + y (5 • b) - x (4 • b)]
  apply hno
  refine barbell_4_4_4 u hu g (q2V b x y 0) (q2V b x y (4 • b)) hq0 hq4
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [u, g, ha2b, zero_add, neg_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) 0 (-x 0)
  · simpa [u, g, zero_add] using eb (a := a) (b := b) (x := x) (y := y) 0 (-x 0)
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) b (-x 0 + y 0)
  · have e1 : b + b = 2 • b := by abel
    have hv : -x 0 + y 0 + y b = 0 + q2V b x y 0 := by simp [q2V]; abel
    simpa [u, g, e1, hv] using eb (a := a) (b := b) (x := x) (y := y) b (-x 0 + y 0)
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) (2 • b) 0
  · have e1 : 2 • b + b = 3 • b := by abel
    dsimp [u, g]; rw [← e1]; simpa [zero_add] using eb (a := a) (b := b) (x := x) (y := y) (2 • b) 0
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) (3 • b) (y (2 • b))
  · have e1 : 3 • b + a = 5 • b := by rw [ha2b]; abel
    dsimp [u, g]; rw [← e1]; exact ea (3 • b) (y (2 • b))
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) (5 • b) (y (2 • b) + x (3 • b))
  · have e1 : 5 • b + b = 6 • b := by abel
    dsimp [u, g]; rw [← e1]; exact eb (5 • b) (y (2 • b) + x (3 • b))
  · have e1 : 4 • b + a = 6 • b := by rw [ha2b]; abel
    dsimp [u, g]; rw [← e1]; exact ea_sub (4 • b) (y (2 • b) + x (3 • b) + y (5 • b))
  · have e1 : 4 • b + b = 5 • b := by abel
    have hv : y (2 • b) + x (3 • b) + y (5 • b) - x (4 • b) + y (4 • b) =
        y (2 • b) + x (3 • b) + q2V b x y (4 • b) := by simp [q2V, e1]; abel
    dsimp [u, g]; have h := eb (a := a) (b := b) (x := x) (y := y) (4 • b) (y (2 • b) + x (3 • b) + y (5 • b) - x (4 • b)); rwa [e1, hv] at h

end CaseA2b

/- ## Section 5: Case 4 (`a = 3 • b` with `ord(b) ≥ 7`) -/

section CaseA3b
variable {B V : Type*} [AddCommGroup B] [AddCommGroup V]
variable {a b : B} {x y : B → V}

/-- Voltage of the 6-cycle `C(i) = (0,i)-b-(1,i+b)-0-(0,i+b)-b-(1,i+2b)-0-(0,i+2b)-b-(1,i+3b)-a-(0,i)`
when `a = 3 • b`. Note `hexV i = c3V (i + b) - c3V i`! -/
def c3V (b : B) (x y : B → V) (i : B) : V := y i + y (i + b) + y (i + 2 • b) - x i

lemma hexV_eq_c3V_diff (ha3b : a = 3 • b) (i : B) :
    hexV a b x y i = c3V b x y (i + b) - c3V b x y i := by
  have e1 : i + b + b = i + 2 • b := by abel
  have e2 : i + b + 2 • b = i + a := by rw [ha3b]; abel
  dsimp [hexV, c3V]; rw [e1, e2]; abel

/-- Under `a = 3 • b` and `ord(b) ≥ 7`, the simple 8-cycle has voltage `c3V i - c3V (i+b) + c3V (i+2b)`. -/
lemma case_a3b_c8 (ha3b : a = 3 • b)
    (hb : b ≠ 0) (h2b : 2 • b ≠ 0) (h3b : 3 • b ≠ 0) (h4b : 4 • b ≠ 0) (h5b : 5 • b ≠ 0)
    (i : B) (h0 : c3V b x y i - c3V b x y (i + b) + c3V b x y (i + 2 • b) = 0) :
    HasPow2 (GNorm a b x y) := by
  -- 8-cycle: (0,i)-b->(1,i+b)-0'->(0,i+b)-a->(1,i+4b)-0'->(0,i+4b)-b->(1,i+5b)-a'->(0,i+2b)-b->(1,i+3b)-a'->(0,i)
  let u : Fin 8 → Bool × B := ![
    (false, i), (true, i + b), (false, i + b), (true, i + 4 • b),
    (false, i + 4 • b), (true, i + 5 • b), (false, i + 2 • b), (true, i + 3 • b)]
  have hu : Function.Injective u := by
    intro p r hpr
    fin_cases p <;> fin_cases r <;> dsimp [u] at hpr
    all_goals first
      | rfl
      | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
      | (have e := congrArg Prod.snd hpr; dsimp at e
         first | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
               | (solve | exfalso; apply hb; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h2b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h2b; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h3b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h3b; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h4b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h4b; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h5b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h5b; linear_combination (norm := abel) -e))
  let g : Fin 8 → V := ![
    0, y i, y i, y i + x (i + b),
    y i + x (i + b), y i + x (i + b) + y (i + 4 • b),
    y i + x (i + b) + y (i + 4 • b) - x (i + 2 • b),
    y i + x (i + b) + y (i + 4 • b) - x (i + 2 • b) + y (i + 2 • b)]
  apply hasPow2_of_8 (walk_to_cycle (by decide) (fun k => ((u k).1, (u k).2, g k)) ?_ ?_)
  · intro p r hpr; exact hu (Prod.ext (congrArg (fun z : Bool × B × V => z.1) hpr) (congrArg (fun z : Bool × B × V => z.2.1) hpr))
  · intro k; fin_cases k <;> dsimp [u, g]
    · simpa using eb (a := a) (b := b) (x := x) (y := y) i 0
    · exact e0' (i + b) _
    · have e1 : i + b + a = i + 4 • b := by rw [ha3b]; abel
      have h := ea (a := a) (b := b) (x := x) (y := y) (i + b) (y i); rwa [e1] at h
    · exact e0' (i + 4 • b) _
    · have e1 : i + 4 • b + b = i + 5 • b := by abel
      have h := eb (a := a) (b := b) (x := x) (y := y) (i + 4 • b) (y i + x (i + b)); rwa [e1] at h
    · have e1 : i + 2 • b + a = i + 5 • b := by rw [ha3b]; abel
      have h := ea_sub (a := a) (b := b) (x := x) (y := y) (i + 2 • b) (y i + x (i + b) + y (i + 4 • b)); rwa [e1] at h
    · have e1 : i + 2 • b + b = i + 3 • b := by abel
      have h := eb (a := a) (b := b) (x := x) (y := y) (i + 2 • b) (y i + x (i + b) + y (i + 4 • b) - x (i + 2 • b)); rwa [e1] at h
    · have e1 : i + a = i + 3 • b := by rw [ha3b]
      have hv : 0 + x i = y i + x (i + b) + y (i + 4 • b) - x (i + 2 • b) + y (i + 2 • b) := by
        have f1 : i + b + b = i + 2 • b := by abel
        have f2 : i + b + 2 • b = i + 3 • b := by abel
        have f3 : i + 2 • b + b = i + 3 • b := by abel
        have f4 : i + 2 • b + 2 • b = i + 4 • b := by abel
        dsimp [c3V] at h0; rw [f1, f2, f3, f4] at h0
        linear_combination (norm := abel) -h0
      simpa [e1, hv] using ea' (a := a) (b := b) (x := x) (y := y) i 0

lemma ord7_coord_inj {n : ℕ} {i : B}
    (hb : b ≠ 0) (h2b : 2 • b ≠ 0) (h3b : 3 • b ≠ 0)
    (h4b : 4 • b ≠ 0) (h5b : 5 • b ≠ 0) (h6b : 6 • b ≠ 0)
    (coords : Fin n → Bool × ℤ)
    (hdec : ∀ p r : Fin n, p ≠ r → (coords p).1 = (coords r).1 →
      (coords p).2 ≠ (coords r).2 ∧ |(coords p).2 - (coords r).2| ≤ 6) :
    Function.Injective (fun k : Fin n => ((coords k).1, i + (coords k).2 • b)) := by
  intro p r hpr
  by_contra hne
  have hs : (coords p).1 = (coords r).1 := congrArg (fun z : Bool × B => z.1) hpr
  have hb_eq : i + (coords p).2 • b = i + (coords r).2 • b := congrArg (fun z : Bool × B => z.2) hpr
  have hsub : ((coords p).2 - (coords r).2) • b = 0 := by
    rw [sub_zsmul]; linear_combination (norm := abel) hb_eq
  obtain ⟨hdne, hdle⟩ := hdec p r hne hs
  set d : ℤ := (coords p).2 - (coords r).2
  have hdle' := abs_le.mp hdle
  have hd : d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 3 ∨ d = -3 ∨
            d = 4 ∨ d = -4 ∨ d = 5 ∨ d = -5 ∨ d = 6 ∨ d = -6 := by omega
  rcases hd with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hsub
  · exact hb (by simpa using hsub)
  · exact hb (by linear_combination (norm := abel) -hsub)
  · exact h2b (by linear_combination (norm := abel) hsub)
  · exact h2b (by linear_combination (norm := abel) -hsub)
  · exact h3b (by linear_combination (norm := abel) hsub)
  · exact h3b (by linear_combination (norm := abel) -hsub)
  · exact h4b (by linear_combination (norm := abel) hsub)
  · exact h4b (by linear_combination (norm := abel) -hsub)
  · exact h5b (by linear_combination (norm := abel) hsub)
  · exact h5b (by linear_combination (norm := abel) -hsub)
  · exact h6b (by linear_combination (norm := abel) hsub)
  · exact h6b (by linear_combination (norm := abel) -hsub)

/-- Barbell `(6, 2, 6)` between `C(i)` and `C(i + 4 • b)` under `a = 3 • b, ord(b) ≥ 7`. -/
lemma case_a3b_bar_CC (ha3b : a = 3 • b)
    (hb : b ≠ 0) (h2b : 2 • b ≠ 0) (h3b : 3 • b ≠ 0)
    (h4b : 4 • b ≠ 0) (h5b : 5 • b ≠ 0) (h6b : 6 • b ≠ 0)
    (i : B) (h1 : c3V b x y i ≠ 0) (h2 : c3V b x y (i + 4 • b) ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  -- C1 = C(i) starting at (true, i+3b):
  --   0:(true,i+3b) --a'-> 1:(false,i) --b-> 2:(true,i+b) --0'-> 3:(false,i+b) --b-> 4:(true,i+2b) --0'-> 5:(false,i+2b) --b-> (0, +c3V i)
  -- Bar (len 2): 0:(true,i+3b) --0'-> 6:(false,i+3b) --a-> 7:(true,i+6b)
  -- C2 = C(i+4b) starting at (true, i+6b):
  --   7:(true,i+6b) --0'-> 8:(false,i+6b) --b-> 9:(true,i+7b) --a'-> 10:(false,i+4b) --b-> 11:(true,i+5b) --0'-> 12:(false,i+5b) --b-> (7, +c3V(i+4b))
  -- Note: false vertices are i, i+b, i+2b, i+3b, i+6b, i+4b, i+5b (7 distinct for ord(b) ≥ 7!)
  --       true vertices are i+3b, i+b, i+2b, i+6b, i+7b, i+5b (6 distinct for ord(b) ≥ 7!)
  let u : Fin 13 → Bool × B := ![
    (true, i + 3 • b), (false, i), (true, i + b), (false, i + b), (true, i + 2 • b), (false, i + 2 • b),
    (false, i + 3 • b),
    (true, i + 6 • b), (false, i + 6 • b), (true, i + 7 • b), (false, i + 4 • b), (true, i + 5 • b), (false, i + 5 • b)]
  have hu : Function.Injective u := by
    let coords : Fin 13 → Bool × ℤ := ![
      (true, 3), (false, 0), (true, 1), (false, 1), (true, 2), (false, 2),
      (false, 3),
      (true, 6), (false, 6), (true, 7), (false, 4), (true, 5), (false, 5)]
    have heq : u = fun k => ((coords k).1, i + (coords k).2 • b) := by
      funext k; fin_cases k <;> dsimp [u, coords] <;> ext <;> try rfl
      all_goals (simp only [zero_zsmul, one_zsmul, zero_add, add_zero]; try abel)
    rw [heq]; exact ord7_coord_inj hb h2b h3b h4b h5b h6b coords (by decide)
  let g : Fin 13 → V := ![
    0, -x i, -x i + y i, -x i + y i, -x i + y i + y (i + b), -x i + y i + y (i + b),
    0,
    x (i + 3 • b), x (i + 3 • b), x (i + 3 • b) + y (i + 6 • b),
    x (i + 3 • b) + y (i + 6 • b) - x (i + 4 • b),
    x (i + 3 • b) + y (i + 6 • b) - x (i + 4 • b) + y (i + 4 • b),
    x (i + 3 • b) + y (i + 6 • b) - x (i + 4 • b) + y (i + 4 • b)]
  refine barbell_6_2_6 u hu g (c3V b x y i) (c3V b x y (i + 4 • b)) h1 h2
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp [u, g]; rw [← ha3b]; simpa [zero_sub] using ea_sub (a := a) (b := b) (x := x) (y := y) i 0
  · dsimp [u, g]; exact eb i (-x i)
  · dsimp [u, g]; exact e0' (i + b) _
  · have e1 : i + b + b = i + 2 • b := by abel
    dsimp [u, g]; rw [← e1]; exact eb (i + b) _
  · dsimp [u, g]; exact e0' (i + 2 • b) _
  · have e1 : i + 2 • b + b = i + 3 • b := by abel
    have hv : -x i + y i + y (i + b) + y (i + 2 • b) = 0 + c3V b x y i := by simp [c3V]; abel
    dsimp [u, g]; rw [← e1, ← hv]; exact eb (i + 2 • b) _
  · dsimp [u, g]; exact e0' (i + 3 • b) 0
  · have e1 : i + 3 • b + a = i + 6 • b := by rw [ha3b]; abel
    dsimp [u, g]; rw [← e1]; simpa [zero_add] using ea (a := a) (b := b) (x := x) (y := y) (i + 3 • b) 0
  · dsimp [u, g]; exact e0' (i + 6 • b) _
  · have e1 : i + 6 • b + b = i + 7 • b := by abel
    dsimp [u, g]; rw [← e1]; exact eb (i + 6 • b) _
  · have e1 : i + 4 • b + a = i + 7 • b := by rw [ha3b]; abel
    dsimp [u, g]; rw [← e1]; exact ea_sub (i + 4 • b) _
  · have e1 : i + 4 • b + b = i + 5 • b := by abel
    dsimp [u, g]; rw [← e1]; exact eb (i + 4 • b) _
  · dsimp [u, g]; exact e0' (i + 5 • b) _
  · have e1 : i + 5 • b + b = i + 6 • b := by abel
    have f1 : i + 4 • b + b = i + 5 • b := by abel
    have f2 : i + 4 • b + 2 • b = i + 6 • b := by abel
    have hv : x (i + 3 • b) + y (i + 6 • b) - x (i + 4 • b) + y (i + 4 • b) + y (i + 5 • b) =
        x (i + 3 • b) + c3V b x y (i + 4 • b) := by simp [c3V, f1, f2]; abel
    dsimp [u, g]; have h := eb (a := a) (b := b) (x := x) (y := y) (i + 5 • b) (x (i + 3 • b) + y (i + 6 • b) - x (i + 4 • b) + y (i + 4 • b)); rwa [e1, hv] at h

/-- Barbell `(6, 2, 6)` between `C(i)` and `H(i + 3 • b)` under `a = 3 • b, ord(b) ≥ 7`. -/
lemma case_a3b_bar_CH (ha3b : a = 3 • b)
    (hb : b ≠ 0) (h2b : 2 • b ≠ 0) (h3b : 3 • b ≠ 0)
    (h4b : 4 • b ≠ 0) (h5b : 5 • b ≠ 0) (h6b : 6 • b ≠ 0)
    (i : B) (h1 : c3V b x y i ≠ 0) (h2 : hexV a b x y (i + 3 • b) ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  -- C1 = C(i) starting at (false, i+2b):
  --   0:(false,i+2b) --b-> 1:(true,i+3b) --a'-> 2:(false,i) --b-> 3:(true,i+b) --0'-> 4:(false,i+b) --b-> 5:(true,i+2b) --0'-> (0, +c3V i)
  -- Bar (len 2): 0:(false,i+2b) --a-> 6:(true,i+5b) --b'-> 7:(false,i+4b)
  -- C2 = H(i+3b) starting at (false, i+4b):
  --   7:(false,i+4b) --0-> 8:(true,i+4b) --b'-> 9:(false,i+3b) --a-> 10:(true,i+6b) --0'-> 11:(false,i+6b) --b-> 12:(true,i+7b) --a'-> (7, +hexV(i+3b))
  -- Note: false vertices: i+2b, i, i+b, i+4b, i+3b, i+6b (6 distinct!)
  --       true vertices: i+3b, i+b, i+2b, i+5b, i+4b, i+6b, i+7b (7 distinct for ord(b) ≥ 7!)
  let u : Fin 13 → Bool × B := ![
    (false, i + 2 • b), (true, i + 3 • b), (false, i), (true, i + b), (false, i + b), (true, i + 2 • b),
    (true, i + 5 • b),
    (false, i + 4 • b), (true, i + 4 • b), (false, i + 3 • b), (true, i + 6 • b), (false, i + 6 • b), (true, i + 7 • b)]
  have hu : Function.Injective u := by
    let coords : Fin 13 → Bool × ℤ := ![
      (false, 2), (true, 3), (false, 0), (true, 1), (false, 1), (true, 2),
      (true, 5),
      (false, 4), (true, 4), (false, 3), (true, 6), (false, 6), (true, 7)]
    have heq : u = fun k => ((coords k).1, i + (coords k).2 • b) := by
      funext k; fin_cases k <;> dsimp [u, coords] <;> ext <;> try rfl
      all_goals (simp only [zero_zsmul, one_zsmul, zero_add, add_zero]; try abel)
    rw [heq]; exact ord7_coord_inj hb h2b h3b h4b h5b h6b coords (by decide)
  let g : Fin 13 → V := ![
    0, y (i + 2 • b), y (i + 2 • b) - x i, y (i + 2 • b) - x i + y i,
    y (i + 2 • b) - x i + y i, y (i + 2 • b) - x i + y i + y (i + b),
    x (i + 2 • b),
    x (i + 2 • b) - y (i + 4 • b), x (i + 2 • b) - y (i + 4 • b),
    x (i + 2 • b) - y (i + 4 • b) - y (i + 3 • b),
    x (i + 2 • b) - y (i + 4 • b) - y (i + 3 • b) + x (i + 3 • b),
    x (i + 2 • b) - y (i + 4 • b) - y (i + 3 • b) + x (i + 3 • b),
    x (i + 2 • b) - y (i + 4 • b) - y (i + 3 • b) + x (i + 3 • b) + y (i + 6 • b)]
  refine barbell_6_2_6 u hu g (c3V b x y i) (hexV a b x y (i + 3 • b)) h1 h2
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have e1 : i + 2 • b + b = i + 3 • b := by abel
    dsimp [u, g]; rw [← e1]; simpa [zero_add] using eb (a := a) (b := b) (x := x) (y := y) (i + 2 • b) 0
  · dsimp [u, g]; rw [← ha3b]; exact ea_sub i _
  · dsimp [u, g]; exact eb i _
  · dsimp [u, g]; exact e0' (i + b) _
  · have e1 : i + b + b = i + 2 • b := by abel
    dsimp [u, g]; rw [← e1]; exact eb (i + b) _
  · have hv : y (i + 2 • b) - x i + y i + y (i + b) = 0 + c3V b x y i := by simp [c3V]; abel
    dsimp [u, g]; rw [← hv]; exact e0' (i + 2 • b) _
  · have e1 : i + 2 • b + a = i + 5 • b := by rw [ha3b]; abel
    dsimp [u, g]; rw [← e1]; simpa [zero_add] using ea (a := a) (b := b) (x := x) (y := y) (i + 2 • b) 0
  · have e1 : i + 4 • b + b = i + 5 • b := by abel
    dsimp [u, g]; rw [← e1]; exact eb_sub (i + 4 • b) _
  · dsimp [u, g]; exact e0 (i + 4 • b) _
  · have e1 : i + 3 • b + b = i + 4 • b := by abel
    dsimp [u, g]; rw [← e1]; exact eb_sub (i + 3 • b) _
  · have e1 : i + 3 • b + a = i + 6 • b := by rw [ha3b]; abel
    dsimp [u, g]; rw [← e1]; exact ea (i + 3 • b) _
  · dsimp [u, g]; exact e0' (i + 6 • b) _
  · have e1 : i + 6 • b + b = i + 7 • b := by abel
    dsimp [u, g]; rw [← e1]; exact eb (i + 6 • b) _
  · have e1 : i + 4 • b + a = i + 7 • b := by rw [ha3b]; abel
    have f1 : i + 3 • b + a = i + 6 • b := by rw [ha3b]; abel
    have f2 : i + 3 • b + b = i + 4 • b := by abel
    have hv : x (i + 2 • b) - y (i + 4 • b) + hexV a b x y (i + 3 • b) + x (i + 4 • b) =
        x (i + 2 • b) - y (i + 4 • b) - y (i + 3 • b) + x (i + 3 • b) + y (i + 6 • b) := by
      simp [hexV, f1, f2]; abel
    dsimp [u, g]; rw [← e1, ← hv]; exact ea' (i + 4 • b) (x (i + 2 • b) - y (i + 4 • b) + hexV a b x y (i + 3 • b))

/-- Complete 6-line proof of Case 4 (`a = 3 • b` with `ord(b) ≥ 7`, including `ℤ/7`!). -/
theorem case_a3b_ge7 (ha3b : a = 3 • b)
    (hb : b ≠ 0) (h2b : 2 • b ≠ 0) (h3b : 3 • b ≠ 0)
    (h4b : 4 • b ≠ 0) (h5b : 5 • b ≠ 0) (h6b : 6 • b ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  by_contra hno
  have hc8 : ∀ i : B, c3V b x y i - c3V b x y (i + b) + c3V b x y (i + 2 • b) ≠ 0 :=
    fun i h => hno (case_a3b_c8 ha3b hb h2b h3b h4b h5b i h)
  have hCC : ∀ i : B, c3V b x y i ≠ 0 → c3V b x y (i + 4 • b) = 0 := by
    intro i hi; by_contra h4; exact hno (case_a3b_bar_CC ha3b hb h2b h3b h4b h5b h6b i hi h4)
  have hCH : ∀ i : B, c3V b x y i ≠ 0 → c3V b x y (i + 3 • b) = c3V b x y (i + 4 • b) := by
    intro i hi
    have hhex : hexV a b x y (i + 3 • b) = 0 := by
      by_contra hne; exact hno (case_a3b_bar_CH ha3b hb h2b h3b h4b h5b h6b i hi hne)
    rw [hexV_eq_c3V_diff ha3b, show i + 3 • b + b = i + 4 • b by abel] at hhex
    linear_combination (norm := abel) -hhex
  -- From hc8 0, at least one of c3V 0, c3V b, c3V (2b) is nonzero!
  have hex : ∃ i0 : B, c3V b x y i0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hc8 0 (by simp [hall])
  obtain ⟨i0, hi0⟩ := hex
  have h4 : c3V b x y (i0 + 4 • b) = 0 := hCC i0 hi0
  have h3 : c3V b x y (i0 + 3 • b) = 0 := (hCH i0 hi0).trans h4
  have h2_nz : c3V b x y (i0 + 2 • b) ≠ 0 := by
    intro h2
    have := hc8 (i0 + 2 • b)
    rw [show i0 + 2 • b + b = i0 + 3 • b by abel, show i0 + 2 • b + 2 • b = i0 + 4 • b by abel,
        h2, h3, h4] at this
    simp at this
  have h6 : c3V b x y (i0 + 6 • b) = 0 := by
    simpa [show i0 + 2 • b + 4 • b = i0 + 6 • b by abel] using hCC (i0 + 2 • b) h2_nz
  have h5 : c3V b x y (i0 + 5 • b) = 0 := by
    have := hCH (i0 + 2 • b) h2_nz
    rw [show i0 + 2 • b + 3 • b = i0 + 5 • b by abel, show i0 + 2 • b + 4 • b = i0 + 6 • b by abel, h6] at this
    exact this
  have hbad := hc8 (i0 + 3 • b)
  rw [show i0 + 3 • b + b = i0 + 4 • b by abel, show i0 + 3 • b + 2 • b = i0 + 5 • b by abel,
      h3, h4, h5] at hbad
  simp at hbad

end CaseA3b

/- ## Section 6: Case 3 (`3 • b = 0`) and Master Dispatch -/

section Case3bZero
variable {B V : Type*} [AddCommGroup B] [AddCommGroup V]
variable {a b : B} {x y : B → V}

/-- Vertical 6-cycle voltage `C_b(i)` when `3 • b = 0`:
`(0,i)-b->(1,i+b)-0'->(0,i+b)-b->(1,i+2b)-0'->(0,i+2b)-b->(1,i)-0'->(0,i)`. -/
def cbV (b : B) (y : B → V) (i : B) : V := y i + y (i + b) + y (i + 2 • b)

lemma cbV_add_b (h3b : 3 • b = 0) (i : B) : cbV b y (i + b) = cbV b y i := by
  have e1 : i + b + b = i + 2 • b := by abel
  have e2 : i + b + 2 • b = i := by linear_combination (norm := abel) h3b
  dsimp [cbV]; rw [e1, e2]; abel

lemma hexV_col_sum (h3b : 3 • b = 0) (i : B) :
    hexV a b x y i + hexV a b x y (i + b) + hexV a b x y (i + 2 • b) =
      cbV b y (i + a) - cbV b y i := by
  have e1 : i + b + b = i + 2 • b := by abel
  have e2 : i + 2 • b + b = i := by linear_combination (norm := abel) h3b
  have e3 : i + b + a = i + a + b := by abel
  have e4 : i + 2 • b + a = i + a + 2 • b := by abel
  dsimp [hexV, cbV]; rw [e1, e2, e3, e4]; abel

/-- Simple 8-cycle in `C_6 × K_2` (`3 • b = 0`, `a ∉ ⟨b⟩`):
if `cbV b y i = 0` and `hexV a b x y i = 0`, then `cycleGraph 8 ⊑ G`!
Walk: `(0,i)-a->(1,i+a)-0'->(0,i+a)-b->(1,i+a+b)-a'->(0,i+b)-b->(1,i+2b)-0'->(0,i+2b)-b->(1,i)-0'->(0,i)`.
Voltage: `x i + y (i+a) - x (i+b) + y (i+b) + y (i+2b) = hexV i + cbV i = 0`! -/
lemma case_3b_c8 (hb : b ≠ 0) (h3b : 3 • b = 0)
    (ha0 : a ≠ 0) (hab : a ≠ b) (ha2b : a ≠ 2 • b)
    (i : B) (hsum : hexV a b x y i + cbV b y i = 0) :
    HasPow2 (GNorm a b x y) := by
  have h2b : 2 • b ≠ 0 := by intro e; exact hb (by linear_combination (norm := abel) h3b - e)
  let u : Fin 8 → Bool × B := ![
    (false, i), (true, i + a), (false, i + a), (true, i + a + b),
    (false, i + b), (true, i + 2 • b), (false, i + 2 • b), (true, i)]
  have hu : Function.Injective u := by
    intro p r hpr
    fin_cases p <;> fin_cases r <;> dsimp [u] at hpr
    all_goals first
      | rfl
      | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
      | (have e := congrArg Prod.snd hpr; dsimp at e
         first | (solve | exfalso; apply hb; linear_combination (norm := abel) e)
               | (solve | exfalso; apply hb; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h2b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h2b; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply ha0; linear_combination (norm := abel) e)
               | (solve | exfalso; apply ha0; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply hab; linear_combination (norm := abel) e)
               | (solve | exfalso; apply hab; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply ha2b; linear_combination (norm := abel) e)
               | (solve | exfalso; apply ha2b; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply ha2b; linear_combination (norm := abel) e - h3b)
               | (solve | exfalso; apply ha2b; linear_combination (norm := abel) -e - h3b)
               | (solve | exfalso; apply hab; linear_combination (norm := abel) e - h3b)
               | (solve | exfalso; apply hab; linear_combination (norm := abel) -e - h3b))
  let g : Fin 8 → V := ![
    0, x i, x i, x i + y (i + a),
    x i + y (i + a) - x (i + b), x i + y (i + a) - x (i + b) + y (i + b),
    x i + y (i + a) - x (i + b) + y (i + b),
    x i + y (i + a) - x (i + b) + y (i + b) + y (i + 2 • b)]
  apply hasPow2_of_8 (walk_to_cycle (by decide) (fun k => ((u k).1, (u k).2, g k)) ?_ ?_)
  · intro p r hpr; exact hu (Prod.ext (congrArg (fun z : Bool × B × V => z.1) hpr) (congrArg (fun z : Bool × B × V => z.2.1) hpr))
  · intro k; fin_cases k <;> dsimp [u, g]
    · simpa using ea (a := a) (b := b) (x := x) (y := y) i 0
    · exact e0' (i + a) _
    · exact eb (i + a) _
    · have e1 : i + b + a = i + a + b := by abel
      have h := ea_sub (a := a) (b := b) (x := x) (y := y) (i + b) (x i + y (i + a)); rwa [e1] at h
    · have e1 : i + b + b = i + 2 • b := by abel
      have h := eb (a := a) (b := b) (x := x) (y := y) (i + b) (x i + y (i + a) - x (i + b)); rwa [e1] at h
    · exact e0' (i + 2 • b) _
    · have e1 : i + 2 • b + b = i := by linear_combination (norm := abel) h3b
      have h := eb (a := a) (b := b) (x := x) (y := y) (i + 2 • b) (x i + y (i + a) - x (i + b) + y (i + b)); rwa [e1] at h
    · have hv : x i + y (i + a) - x (i + b) + y (i + b) + y (i + 2 • b) = 0 := by
        dsimp [hexV, cbV] at hsum; linear_combination (norm := abel) hsum
      simpa [hv] using e0' (a := a) (b := b) (x := x) (y := y) i 0

lemma ord3b_zsmul_ne
    (hb : b ≠ 0) (h3b : 3 • b = 0)
    (ha0 : a ≠ 0) (hab : a ≠ b) (ha2b : a ≠ 2 • b)
    (h2a0 : 2 • a ≠ 0) (h2ab : 2 • a ≠ b) (h2a2b : 2 • a ≠ 2 • b)
    (da db : ℤ) (hdne : da ≠ 0 ∨ db % 3 ≠ 0) (hda : |da| ≤ 2) (hdb : |db| ≤ 2) :
    da • a + db • b ≠ 0 := by
  have h2b : 2 • b ≠ 0 := by intro e; exact hb (by linear_combination (norm := abel) h3b - e)
  intro hsub
  have hda0 := abs_le.mp hda; have hdb0 := abs_le.mp hdb
  -- Reduce db to {0, 1, 2} using 3•b = 0!
  have hred : ∀ d : ℤ, -2 ≤ d → d ≤ 2 → (d = 0 ∨ d = 1 ∨ d = 2 ∨ d = -1 ∨ d = -2) := by omega
  have hda' : da = 0 ∨ da = 1 ∨ da = -1 ∨ da = 2 ∨ da = -2 := by omega
  rcases hda' with rfl | rfl | rfl | rfl | rfl <;>
  rcases hred db hdb0.1 hdb0.2 with rfl | rfl | rfl | rfl | rfl <;>
  (try simp only [zero_zsmul, one_zsmul, neg_zsmul, zero_add, add_zero] at hsub)
  · omega
  · exact hb (by linear_combination (norm := abel) hsub)
  · exact h2b (by linear_combination (norm := abel) hsub)
  · exact hb (by linear_combination (norm := abel) -hsub)
  · exact h2b (by linear_combination (norm := abel) -hsub)
  · exact ha0 (by linear_combination (norm := abel) hsub)
  · exact ha2b (by linear_combination (norm := abel) hsub - h3b)
  · exact hab (by linear_combination (norm := abel) hsub - h3b)
  · exact hab (by linear_combination (norm := abel) hsub)
  · exact ha2b (by linear_combination (norm := abel) hsub)
  · exact ha0 (by linear_combination (norm := abel) -hsub)
  · exact hab (by linear_combination (norm := abel) -hsub)
  · exact ha2b (by linear_combination (norm := abel) -hsub)
  · exact ha2b (by linear_combination (norm := abel) -hsub - h3b)
  · exact hab (by linear_combination (norm := abel) -hsub - h3b)
  · exact h2a0 (by linear_combination (norm := abel) hsub)
  · exact h2a2b (by linear_combination (norm := abel) hsub - h3b)
  · exact h2ab (by linear_combination (norm := abel) hsub - h3b)
  · exact h2ab (by linear_combination (norm := abel) hsub)
  · exact h2a2b (by linear_combination (norm := abel) hsub)
  · exact h2a0 (by linear_combination (norm := abel) -hsub)
  · exact h2ab (by linear_combination (norm := abel) -hsub)
  · exact h2a2b (by linear_combination (norm := abel) -hsub)
  · exact h2a2b (by linear_combination (norm := abel) -hsub - h3b)
  · exact h2ab (by linear_combination (norm := abel) -hsub - h3b)

lemma ord3b_coord_inj2 {n : ℕ} {i : B}
    (hb : b ≠ 0) (h3b : 3 • b = 0)
    (ha0 : a ≠ 0) (hab : a ≠ b) (ha2b : a ≠ 2 • b)
    (h2a0 : 2 • a ≠ 0) (h2ab : 2 • a ≠ b) (h2a2b : 2 • a ≠ 2 • b)
    (coords : Fin n → Bool × ℤ × ℤ)
    (hdec : ∀ p r : Fin n, p ≠ r → (coords p).1 = (coords r).1 →
      ((coords p).2.1 ≠ (coords r).2.1 ∨ ((coords p).2.2 - (coords r).2.2) % 3 ≠ 0) ∧
      |(coords p).2.1 - (coords r).2.1| ≤ 2 ∧ |(coords p).2.2 - (coords r).2.2| ≤ 2) :
    Function.Injective (fun k : Fin n => ((coords k).1, i + (coords k).2.1 • a + (coords k).2.2 • b)) := by
  intro p r hpr
  by_contra hne
  have hs : (coords p).1 = (coords r).1 := congrArg (fun z : Bool × B => z.1) hpr
  have hb_eq : i + (coords p).2.1 • a + (coords p).2.2 • b =
      i + (coords r).2.1 • a + (coords r).2.2 • b := congrArg (fun z : Bool × B => z.2) hpr
  have hsub : ((coords p).2.1 - (coords r).2.1) • a + ((coords p).2.2 - (coords r).2.2) • b = 0 := by
    rw [sub_zsmul, sub_zsmul]; linear_combination (norm := abel) hb_eq
  obtain ⟨hdne, hda, hdb⟩ := hdec p r hne hs
  exact ord3b_zsmul_ne hb h3b ha0 hab ha2b h2a0 h2ab h2a2b _ _ (by omega) hda hdb hsub

lemma ord3b_coord_inj {n : ℕ} {i : B}
    (hb : b ≠ 0) (h3b : 3 • b = 0)
    (ha0 : a ≠ 0) (hab : a ≠ b) (ha2b : a ≠ 2 • b)
    (h2a0 : 2 • a ≠ 0) (h2ab : 2 • a ≠ b) (h2a2b : 2 • a ≠ 2 • b)
    (h3a0 : 3 • a ≠ 0) (h3ab : 3 • a ≠ b) (h3a2b : 3 • a ≠ 2 • b)
    (coords : Fin n → Bool × ℤ × ℤ)
    (hdec : ∀ p r : Fin n, p ≠ r → (coords p).1 = (coords r).1 →
      ((coords p).2.1 ≠ (coords r).2.1 ∨ ((coords p).2.2 - (coords r).2.2) % 3 ≠ 0) ∧
      |(coords p).2.1 - (coords r).2.1| ≤ 3 ∧ |(coords p).2.2 - (coords r).2.2| ≤ 2) :
    Function.Injective (fun k : Fin n => ((coords k).1, i + (coords k).2.1 • a + (coords k).2.2 • b)) := by
  intro p r hpr
  by_contra hne
  have hs : (coords p).1 = (coords r).1 := congrArg (fun z : Bool × B => z.1) hpr
  have hb_eq : i + (coords p).2.1 • a + (coords p).2.2 • b =
      i + (coords r).2.1 • a + (coords r).2.2 • b := congrArg (fun z : Bool × B => z.2) hpr
  have hsub : ((coords p).2.1 - (coords r).2.1) • a + ((coords p).2.2 - (coords r).2.2) • b = 0 := by
    rw [sub_zsmul, sub_zsmul]; linear_combination (norm := abel) hb_eq
  obtain ⟨hdne, hda, hdb⟩ := hdec p r hne hs
  set da : ℤ := (coords p).2.1 - (coords r).2.1
  set db : ℤ := (coords p).2.2 - (coords r).2.2
  have hda0 := abs_le.mp hda; have hdb0 := abs_le.mp hdb
  by_cases hle2 : |da| ≤ 2
  · exact ord3b_zsmul_ne hb h3b ha0 hab ha2b h2a0 h2ab h2a2b da db (by omega) hle2 hdb hsub
  · have hda3 : da = 3 ∨ da = -3 := by have := lt_abs.mp (lt_of_not_ge hle2); omega
    have hdb' : db = 0 ∨ db = 1 ∨ db = 2 ∨ db = -1 ∨ db = -2 := by omega
    rcases hda3 with h1 | h1 <;> rcases hdb' with h2 | h2 | h2 | h2 | h2 <;>
    (rw [h1, h2] at hsub; try simp only [zero_zsmul, one_zsmul, neg_zsmul, zero_add, add_zero] at hsub)
    · exact h3a0 (by linear_combination (norm := abel) hsub)
    · exact h3a2b (by linear_combination (norm := abel) hsub - h3b)
    · exact h3ab (by linear_combination (norm := abel) hsub - h3b)
    · exact h3ab (by linear_combination (norm := abel) hsub)
    · exact h3a2b (by linear_combination (norm := abel) hsub)
    · exact h3a0 (by linear_combination (norm := abel) -hsub)
    · exact h3ab (by linear_combination (norm := abel) -hsub)
    · exact h3a2b (by linear_combination (norm := abel) -hsub)
    · exact h3a2b (by linear_combination (norm := abel) -hsub - h3b)
    · exact h3ab (by linear_combination (norm := abel) -hsub - h3b)

/-- Barbell `(6, 2, 6)` in `C_6 × P_3` (`3 • b = 0`, `a, 2a ∉ ⟨b⟩`):
between `C_b(i)` and `H(i + a)`: if `cbV b y i ≠ 0` and `hexV a b x y (i + a) ≠ 0`, then `HasPow2`! -/
lemma case_3b_bar_CH (hb : b ≠ 0) (h3b : 3 • b = 0)
    (ha0 : a ≠ 0) (hab : a ≠ b) (ha2b : a ≠ 2 • b)
    (h2a0 : 2 • a ≠ 0) (h2ab : 2 • a ≠ b) (h2a2b : 2 • a ≠ 2 • b)
    (i : B) (hc : cbV b y i ≠ 0) (hh : hexV a b x y (i + a) ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  have h2b : 2 • b ≠ 0 := by intro e; exact hb (by linear_combination (norm := abel) h3b - e)
  -- C1 = C_b(i) starting at (false, i):
  --   0:(false,i) -b-> 1:(true,i+b) -0'-> 2:(false,i+b) -b-> 3:(true,i+2b) -0'-> 4:(false,i+2b) -b-> 5:(true,i) -0'-> (0, +cbV i)
  -- Bar (len 2): 0:(false,i) -a-> 6:(true,i+a) -0'-> 7:(false,i+a)
  -- C2 = H(i+a) starting at (false, i+a):
  --   7:(false,i+a) -a-> 8:(true,i+2a) -0'-> 9:(false,i+2a) -b-> 10:(true,i+2a+b) -a'-> 11:(false,i+a+b) -0-> 12:(true,i+a+b) -b'-> (7, +hexV(i+a))
  let u : Fin 13 → Bool × B := ![
    (false, i), (true, i + b), (false, i + b), (true, i + 2 • b), (false, i + 2 • b), (true, i),
    (true, i + a),
    (false, i + a), (true, i + 2 • a), (false, i + 2 • a), (true, i + 2 • a + b), (false, i + a + b), (true, i + a + b)]
  have hu : Function.Injective u := by
    let coords : Fin 13 → Bool × ℤ × ℤ := ![
      (false, 0, 0), (true, 0, 1), (false, 0, 1), (true, 0, 2), (false, 0, 2), (true, 0, 0),
      (true, 1, 0),
      (false, 1, 0), (true, 2, 0), (false, 2, 0), (true, 2, 1), (false, 1, 1), (true, 1, 1)]
    have heq : u = fun k => ((coords k).1, i + (coords k).2.1 • a + (coords k).2.2 • b) := by
      funext k; fin_cases k <;> dsimp [u, coords] <;> ext <;> try rfl
      all_goals (simp only [zero_zsmul, one_zsmul, zero_add, add_zero]; try abel)
    rw [heq]; exact ord3b_coord_inj2 hb h3b ha0 hab ha2b h2a0 h2ab h2a2b coords (by decide)
  let g : Fin 13 → V := ![
    0, y i, y i, y i + y (i + b), y i + y (i + b), y i + y (i + b) + y (i + 2 • b),
    x i,
    x i, x i + x (i + a), x i + x (i + a), x i + x (i + a) + y (i + 2 • a),
    x i + x (i + a) + y (i + 2 • a) - x (i + a + b),
    x i + x (i + a) + y (i + 2 • a) - x (i + a + b)]
  refine barbell_6_2_6 u hu g (cbV b y i) (hexV a b x y (i + a)) hc hh
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [u, g] using eb (a := a) (b := b) (x := x) (y := y) i 0
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) (i + b) _
  · have e1 : i + b + b = i + 2 • b := by abel
    simpa [u, g, e1] using eb (a := a) (b := b) (x := x) (y := y) (i + b) _
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) (i + 2 • b) _
  · have e1 : i + 2 • b + b = i := by linear_combination (norm := abel) h3b
    dsimp [u, g]; have h := eb (a := a) (b := b) (x := x) (y := y) (i + 2 • b) (y i + y (i + b)); rwa [e1] at h
  · have hv : y i + y (i + b) + y (i + 2 • b) = 0 + cbV b y i := by simp [cbV]
    simpa [u, g, hv] using e0' (a := a) (b := b) (x := x) (y := y) i _
  · simpa [u, g] using ea (a := a) (b := b) (x := x) (y := y) i 0
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) (i + a) _
  · have e1 : i + a + a = i + 2 • a := by abel
    simpa [u, g, e1] using ea (a := a) (b := b) (x := x) (y := y) (i + a) _
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) (i + 2 • a) _
  · simpa [u, g] using eb (a := a) (b := b) (x := x) (y := y) (i + 2 • a) _
  · have e1 : i + a + b + a = i + 2 • a + b := by abel
    dsimp [u, g]; have h := ea_sub (a := a) (b := b) (x := x) (y := y) (i + a + b) (x i + x (i + a) + y (i + 2 • a)); rwa [e1] at h
  · simpa [u, g] using e0 (a := a) (b := b) (x := x) (y := y) (i + a + b) _
  · have f1 : i + a + a = i + 2 • a := by abel
    have hv : x i + hexV a b x y (i + a) + y (i + a) =
        x i + x (i + a) + y (i + 2 • a) - x (i + a + b) := by simp [hexV, f1]; abel
    simpa [u, g, hv] using eb' (a := a) (b := b) (x := x) (y := y) (i + a) (x i + hexV a b x y (i + a))

/-- Horizontal barbell `(6, 2, 6)` between `H(0)` and `H(2a)` when `3 • b = 0` and
`a, 2a, 3a ∉ ⟨b⟩`! -/
lemma case_3b_bar_2a (hb : b ≠ 0) (h3b : 3 • b = 0)
    (ha0 : a ≠ 0) (hab : a ≠ b) (ha2b : a ≠ 2 • b)
    (h2a0 : 2 • a ≠ 0) (h2ab : 2 • a ≠ b) (h2a2b : 2 • a ≠ 2 • b)
    (h3a0 : 3 • a ≠ 0) (h3ab : 3 • a ≠ b) (h3a2b : 3 • a ≠ 2 • b)
    (h1 : hexV a b x y 0 ≠ 0) (h2 : hexV a b x y (2 • a) ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  have h2b : 2 • b ≠ 0 := by intro e; exact hb (by linear_combination (norm := abel) h3b - e)
  let u : Fin 13 → Bool × B := ![
    (false, a), (true, a + b), (false, b), (true, b), (false, 0), (true, a),
    (true, 2 • a),
    (false, 2 • a), (true, 3 • a), (false, 3 • a), (true, 3 • a + b), (false, 2 • a + b), (true, 2 • a + b)]
  have hu : Function.Injective u := by
    let coords : Fin 13 → Bool × ℤ × ℤ := ![
      (false, 1, 0), (true, 1, 1), (false, 0, 1), (true, 0, 1), (false, 0, 0), (true, 1, 0),
      (true, 2, 0),
      (false, 2, 0), (true, 3, 0), (false, 3, 0), (true, 3, 1), (false, 2, 1), (true, 2, 1)]
    have heq : u = fun k => ((coords k).1, (0 : B) + (coords k).2.1 • a + (coords k).2.2 • b) := by
      funext k; fin_cases k <;> dsimp [u, coords] <;> ext <;> try rfl
      all_goals (simp only [zero_zsmul, one_zsmul, zero_add, add_zero]; try abel)
    rw [heq]; exact ord3b_coord_inj hb h3b ha0 hab ha2b h2a0 h2ab h2a2b h3a0 h3ab h3a2b coords (by decide)
  let g : Fin 13 → V := ![
    0, y a, y a - x b, y a - x b, y a - x b - y 0, y a - x b - y 0 + x 0,
    x a,
    x a, x a + x (2 • a), x a + x (2 • a), x a + x (2 • a) + y (3 • a),
    x a + x (2 • a) + y (3 • a) - x (2 • a + b),
    x a + x (2 • a) + y (3 • a) - x (2 • a + b)]
  refine barbell_6_2_6 u hu g (hexV a b x y 0) (hexV a b x y (2 • a)) h1 h2
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [u, g] using eb (a := a) (b := b) (x := x) (y := y) a 0
  · simpa [u, g, add_comm, sub_add_cancel] using ea' (a := a) (b := b) (x := x) (y := y) b (y a - x b)
  · simpa [u, g] using e0 (a := a) (b := b) (x := x) (y := y) b (y a - x b)
  · simpa [u, g, zero_add, sub_add_cancel] using eb' (a := a) (b := b) (x := x) (y := y) 0 (y a - x b - y 0)
  · simpa [u, g, zero_add] using ea (a := a) (b := b) (x := x) (y := y) 0 (y a - x b - y 0)
  · have hv : y a - x b - y 0 + x 0 = 0 + hexV a b x y 0 := by simp [hexV]; abel
    simpa [u, g, hv] using e0' (a := a) (b := b) (x := x) (y := y) a (0 + hexV a b x y 0)
  · have hb2 : a + a = 2 • a := by abel
    simpa [u, g, hb2] using ea (a := a) (b := b) (x := x) (y := y) a 0
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) (2 • a) (x a)
  · have h3 : 2 • a + a = 3 • a := by abel
    dsimp [u, g]; have h := ea (a := a) (b := b) (x := x) (y := y) (2 • a) (x a); rwa [h3] at h
  · simpa [u, g] using e0' (a := a) (b := b) (x := x) (y := y) (3 • a) (x a + x (2 • a))
  · simpa [u, g] using eb (a := a) (b := b) (x := x) (y := y) (3 • a) (x a + x (2 • a))
  · have h3b' : 2 • a + b + a = 3 • a + b := by abel
    dsimp [u, g]; have h := ea_sub (a := a) (b := b) (x := x) (y := y) (2 • a + b) (x a + x (2 • a) + y (3 • a)); rwa [h3b'] at h
  · simpa [u, g] using e0 (a := a) (b := b) (x := x) (y := y) (2 • a + b) _
  · have f1 : 2 • a + a = 3 • a := by abel
    have hv : x a + hexV a b x y (2 • a) + y (2 • a) =
        x a + x (2 • a) + y (3 • a) - x (2 • a + b) := by simp [hexV, f1]; abel
    dsimp [u, g]; have h := eb' (a := a) (b := b) (x := x) (y := y) (2 • a) (x a + hexV a b x y (2 • a)); rwa [hv] at h

/-- Subcase 3a: `B = ℤ/3 × ℤ/3` (`3 • a = 0, 3 • b = 0`, `a ∉ ⟨b⟩`) with `cbV = 0`, `caV = 0`,
and `hexV ≠ 0` everywhere!
1. `theta_2_10_4` (which has ZERO base collisions in `ℤ/3 × ℤ/3`!) forces `hexV` to be circulant.
2. Our 1 explicit 16-cycle kills the circulant matrix! -/
lemma case_3b_z33 (hb : b ≠ 0) (h3b : 3 • b = 0) (h3a : 3 • a = 0)
    (ha0 : a ≠ 0) (hab : a ≠ b) (ha2b : a ≠ 2 • b)
    (h2a0 : 2 • a ≠ 0) (h2ab : 2 • a ≠ b) (h2a2b : 2 • a ≠ 2 • b)
    (hcb : ∀ i : B, cbV b y i = 0) (hca : ∀ i : B, cbV a x i = 0)
    (hhex_nz : ∀ i : B, hexV a b x y i ≠ 0) :
    HasPow2 (GNorm a b x y) := by
  by_contra hno
  have h2b : 2 • b ≠ 0 := by intro e; exact hb (by linear_combination (norm := abel) h3b - e)
  -- Helper: linear combinations p•a + q•b ≠ 0 for (p,q) mod 3 ≠ (0,0)!
  let pt : ZMod 3 × ZMod 3 → B := fun z => z.1.val • a + z.2.val • b
  have hpt_inj : Function.Injective pt := by
    rintro ⟨r1, c1⟩ ⟨r2, c2⟩ h
    by_contra hne
    have hsub : ((r1.val : ℤ) - (r2.val : ℤ)) • a + ((c1.val : ℤ) - (c2.val : ℤ)) • b = 0 := by
      dsimp [pt] at h; rw [sub_zsmul, sub_zsmul]; simp only [natCast_zsmul]; linear_combination (norm := abel) h
    have hr1 : r1.val < 3 := r1.val_lt; have hr2 : r2.val < 3 := r2.val_lt
    have hc1 : c1.val < 3 := c1.val_lt; have hc2 : c2.val < 3 := c2.val_lt
    have hne' : (r1.val : ℤ) - r2.val ≠ 0 ∨ ((c1.val : ℤ) - c2.val) % 3 ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hne (Prod.ext (ZMod.val_injective 3 (by change r1.val = r2.val; omega)) (ZMod.val_injective 3 (by change c1.val = c2.val; omega)))
    exact ord3b_zsmul_ne hb h3b ha0 hab ha2b h2a0 h2ab h2a2b _ _ hne' (abs_le.mpr ⟨by omega, by omega⟩) (abs_le.mpr ⟨by omega, by omega⟩) hsub
  have hpt_a : ∀ r c : ZMod 3, pt (r + 1, c) = pt (r, c) + a := by
    intro r c; fin_cases r <;> dsimp [pt]
    · change (1 : ℕ) • a + c.val • b = (0 : ℕ) • a + c.val • b + a; abel
    · change (2 : ℕ) • a + c.val • b = (1 : ℕ) • a + c.val • b + a; abel
    · change (0 : ℕ) • a + c.val • b = (2 : ℕ) • a + c.val • b + a; linear_combination (norm := abel) -h3a
  have hpt_b : ∀ r c : ZMod 3, pt (r, c + 1) = pt (r, c) + b := by
    intro r c; fin_cases c <;> dsimp [pt]
    · change r.val • a + (1 : ℕ) • b = r.val • a + (0 : ℕ) • b + b; abel
    · change r.val • a + (2 : ℕ) • b = r.val • a + (1 : ℕ) • b + b; abel
    · change r.val • a + (0 : ℕ) • b = r.val • a + (2 : ℕ) • b + b; linear_combination (norm := abel) -h3b
  -- Step 1: Theta(2, 10, 4) at any shift i gives hexV i + hexV (i+a) + hexV (i+b) = 0!
  -- Because the 2x2 sum hexV i + hexV (i+a) + hexV (i+b) + hexV (i+a+b) = hexV (i+2a+2b) ≠ 0!
  have hcol_sum : ∀ i : B, hexV a b x y i + hexV a b x y (i + b) + hexV a b x y (i + 2 • b) = 0 := by
    intro i; rw [hexV_col_sum h3b, hcb, hcb, sub_self]
  have hrow_sum : ∀ i : B, hexV a b x y i + hexV a b x y (i + a) + hexV a b x y (i + 2 • a) = 0 := by
    intro i
    have hsw : hexV b a y x i + hexV b a y x (i + a) + hexV b a y x (i + 2 • a) = cbV a x (i + b) - cbV a x i :=
      hexV_col_sum h3a i
    rw [hca, hca, sub_self] at hsw
    have hneg : ∀ j : B, hexV b a y x j = -hexV a b x y j := fun j => by dsimp [hexV]; abel
    simp only [hneg] at hsw
    linear_combination (norm := abel) -hsw
  have hstar_zero : ∀ i : B, hexV a b x y i + hexV a b x y (i + a) + hexV a b x y (i + b) = 0 := by
    intro i
    by_contra hne
    -- Apply theta_2_10_4 translated by i!
    have hno' : ¬ HasPow2 (GNorm a b (fun j => x (j + i)) (fun j => y (j + i))) :=
      fun h => hno (hasPow2_mono (gnorm_translate i) h)
    let x' := fun j => x (j + i)
    let y' := fun j => y (j + i)
    let u0 : Fin 15 → Bool × ZMod 3 × ZMod 3 := ![
      (true, (2, 1)), (true, (1, 2)),
      (false, (1, 1)),
      (false, (2, 1)), (true, (2, 2)), (false, (1, 2)),
      (false, (2, 0)), (true, (2, 0)), (false, (1, 0)), (true, (1, 0)),
      (false, (0, 0)), (true, (0, 1)), (false, (0, 1)), (true, (0, 2)), (false, (0, 2))]
    have hu0 : Function.Injective u0 := by decide
    let u : Fin 15 → Bool × B := fun k => ((u0 k).1, pt (u0 k).2)
    have hu : Function.Injective u := fun p r hpr =>
      hu0 (Prod.ext (congrArg (fun z : Bool × B => z.1) hpr) (hpt_inj (congrArg (fun z : Bool × B => z.2) hpr)))
    let vP : V := -x' (a + b) + y' (a + b)
    let vR : V := y' (2 • a + b) - x' (a + 2 • b)
    let vQ : V := -y' (2 • a) - x' a - x' 0 + y' 0 + y' b + x' (2 • b)
    have hvPR : vP - vR = -hexV a b x' y' (a + b) := by
      have e1 : a + b + a = 2 • a + b := by abel
      have e2 : a + b + b = a + 2 • b := by abel
      dsimp [vP, vR, hexV]; rw [e1, e2]; abel
    have hvPQ : vP - vQ = hexV a b x' y' 0 + hexV a b x' y' a + hexV a b x' y' b := by
      have e1 : a + a = 2 • a := by abel
      have e2 : b + b = 2 • b := by abel
      have e3 : b + a = a + b := by abel
      dsimp [vP, vQ, hexV]; rw [e1, e2, e3]; abel
    have htr : ∀ j : B, hexV a b x' y' j = hexV a b x y (i + j) := by
      intro j
      have e1 : j + i = i + j := add_comm _ _
      have e2 : j + a + i = i + j + a := by abel
      have e3 : j + b + i = i + j + b := by abel
      simp [hexV, x', y', e1, e2, e3]
    have hPQ : vP ≠ vQ := by
      intro e; have := sub_eq_zero.mpr e; rw [hvPQ, htr, htr, htr, add_zero] at this; exact hne this
    have hRP : vR ≠ vP := by
      intro e; have := sub_eq_zero.mpr e.symm; rw [hvPR, htr] at this; exact hhex_nz _ (by simpa using this)
    have hQR : vQ ≠ vR := by
      intro e
      have h1 : vP - vQ = vP - vR := by rw [e]
      rw [hvPQ, hvPR, htr, htr, htr, htr, add_zero] at h1
      have h2x2 : hexV a b x y i + hexV a b x y (i + a) + hexV a b x y (i + b) + hexV a b x y (i + (a + b)) =
          hexV a b x y (i + 2 • a + 2 • b) := by
        have r0 := hrow_sum i
        have r1 := hrow_sum (i + b)
        have c0 := hcol_sum (i + 2 • a)
        rw [show i + b + a = i + (a + b) by abel, show i + b + 2 • a = i + 2 • a + b by abel] at r1
        linear_combination (norm := abel) r0 + r1 - c0
      exact hhex_nz (i + 2 • a + 2 • b) (by linear_combination (norm := abel) -h2x2 + h1)
    let g : Fin 15 → V := ![
      0, 0, -x' (a + b),
      0, y' (2 • a + b), y' (2 • a + b) - x' (a + 2 • b),
      -y' (2 • a), -y' (2 • a), -y' (2 • a) - x' a, -y' (2 • a) - x' a,
      -y' (2 • a) - x' a - x' 0, -y' (2 • a) - x' a - x' 0 + y' 0,
      -y' (2 • a) - x' a - x' 0 + y' 0, -y' (2 • a) - x' a - x' 0 + y' 0 + y' b,
      -y' (2 • a) - x' a - x' 0 + y' 0 + y' b]
    apply hno'
    refine theta_2_10_4 u hu g vP vQ vR hPQ hQR hRP
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals dsimp [u, u0, pt, g, vP, vQ, vR]
    all_goals simp only [ZMod.val_zero, ZMod.val_one, show (2 : ZMod 3).val = 2 by decide, zero_nsmul, one_nsmul, zero_add, add_zero]
    · have e1 : a + b + a = 2 • a + b := by abel
      have h := ea' (a := a) (b := b) (x := x') (y := y') (a + b) (-x' (a + b)); rwa [e1, neg_add_cancel] at h
    · have e1 : a + b + b = a + 2 • b := by abel
      have h := eb (a := a) (b := b) (x := x') (y := y') (a + b) (-x' (a + b)); rwa [e1] at h
    · exact e0' (2 • a + b) 0
    · have e1 : 2 • a + b + b = 2 • a + 2 • b := by abel
      have h := eb (a := a) (b := b) (x := x') (y := y') (2 • a + b) 0; rwa [e1, zero_add] at h
    · have e1 : a + 2 • b + a = 2 • a + 2 • b := by abel
      have h := ea_sub (a := a) (b := b) (x := x') (y := y') (a + 2 • b) (y' (2 • a + b)); rwa [e1] at h
    · exact e0 (a + 2 • b) _
    · have h := eb' (a := a) (b := b) (x := x') (y := y') (2 • a) (-y' (2 • a)); rwa [neg_add_cancel] at h
    · exact e0 (2 • a) _
    · have e1 : a + a = 2 • a := by abel
      have h := ea_sub (a := a) (b := b) (x := x') (y := y') a (-y' (2 • a)); rwa [e1] at h
    · exact e0 a _
    · have h := ea_sub (a := a) (b := b) (x := x') (y := y') 0 (-y' (2 • a) - x' a); rwa [zero_add] at h
    · have h := eb (a := a) (b := b) (x := x') (y := y') 0 (-y' (2 • a) - x' a - x' 0); rwa [zero_add] at h
    · exact e0' b _
    · have e1 : b + b = 2 • b := by abel
      have h := eb (a := a) (b := b) (x := x') (y := y') b (-y' (2 • a) - x' a - x' 0 + y' 0); rwa [e1] at h
    · exact e0' (2 • b) _
    · have e1 : 2 • b + a = a + 2 • b := by abel
      have h := ea (a := a) (b := b) (x := x') (y := y') (2 • b) (-y' (2 • a) - x' a - x' 0 + y' 0 + y' b); rwa [e1] at h
  -- Step 2: Our 1 explicit 16-cycle in Z/3 x Z/3!
  -- Base walk: (0,(0,0)), (1,(0,0)), (0,(2,0)), (1,(2,0)), (0,(1,0)), (1,(1,0)), (0,(1,2)), (1,(1,2)),
  --            (0,(0,2)), (1,(0,2)), (0,(2,2)), (1,(2,0)), (0,(2,0)), (1,(2,1)), (0,(2,1)), (1,(0,1))
  -- Only repeated base vertices: (1,(2,0)) [idx 3 vs 11] and (0,(2,0)) [idx 2 vs 12],
  -- with voltage difference = hexV (pt (0, 1)) ≠ 0!!
  let w : Fin 16 → Bool × ZMod 3 × ZMod 3 := ![
    (false, (0, 0)), (true, (0, 0)), (false, (2, 0)), (true, (2, 0)),
    (false, (1, 0)), (true, (1, 0)), (false, (1, 2)), (true, (1, 2)),
    (false, (0, 2)), (true, (0, 2)), (false, (2, 2)), (true, (2, 0)),
    (false, (2, 0)), (true, (2, 1)), (false, (2, 1)), (true, (0, 1))]
  let g0 : V := 0
  let g1 : V := 0
  let g2 : V := -x (pt (2, 0))
  let g3 : V := -x (pt (2, 0))
  let g4 : V := -x (pt (2, 0)) - x (pt (1, 0))
  let g5 : V := -x (pt (2, 0)) - x (pt (1, 0))
  let g6 : V := -x (pt (2, 0)) - x (pt (1, 0)) - y (pt (1, 2))
  let g7 : V := -x (pt (2, 0)) - x (pt (1, 0)) - y (pt (1, 2))
  let g8 : V := -x (pt (2, 0)) - x (pt (1, 0)) - y (pt (1, 2)) - x (pt (0, 2))
  let g9 : V := -x (pt (2, 0)) - x (pt (1, 0)) - y (pt (1, 2)) - x (pt (0, 2))
  let g10 : V := -x (pt (2, 0)) - x (pt (1, 0)) - y (pt (1, 2)) - x (pt (0, 2)) - x (pt (2, 2))
  let g11 : V := -x (pt (2, 0)) - x (pt (1, 0)) - y (pt (1, 2)) - x (pt (0, 2)) - x (pt (2, 2)) + y (pt (2, 2))
  let g12 : V := g11
  let g13 : V := g11 + y (pt (2, 0))
  let g14 : V := g13
  let g15 : V := y (pt (0, 0))
  let gv : Fin 16 → V := ![g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15]
  -- Express g11 - g3 = hexV (pt (1, 2)) [nonzero!] and check g14 + x (pt (2, 1)) = g15!
  have hca2 : x (pt (0, 2)) + x (pt (1, 2)) + x (pt (2, 2)) = 0 := by
    have := hca (2 • b)
    have e0' : 2 • b = pt (0, 2) := by dsimp [pt]; simp [ZMod.val_zero, show (2 : ZMod 3).val = 2 by decide]
    have e1 : 2 • b + a = pt (1, 2) := by dsimp [pt]; simp [ZMod.val_one, show (2 : ZMod 3).val = 2 by decide]; abel
    have e2 : 2 • b + 2 • a = pt (2, 2) := by dsimp [pt]; simp [show (2 : ZMod 3).val = 2 by decide]; abel
    dsimp [cbV] at this; rwa [e1, e2, e0'] at this
  have h_diff : g11 - g3 = hexV a b x y (pt (1, 2)) := by
    dsimp [g11, g3, hexV]
    rw [← hpt_a 1 2, ← hpt_b 1 2]
    simp only [show (1 : ZMod 3) + 1 = 2 by decide, show (2 : ZMod 3) + 1 = 0 by decide]
    linear_combination (norm := abel) -hca2
  have h_close : g14 + x (pt (2, 1)) = g15 := by
    have heq_12_20 : hexV a b x y (pt (1, 2)) = hexV a b x y (pt (2, 0)) := by
      have s1 := hstar_zero (pt (0, 0))
      have s3 := hstar_zero (pt (0, 2))
      have r0 := hrow_sum (pt (0, 0))
      have c0 := hcol_sum (pt (0, 0))
      have f : ∀ (r c : ZMod 3), pt (r, c) + a = pt (r + 1, c) := fun r c => (hpt_a r c).symm
      have fb : ∀ (r c : ZMod 3), pt (r, c) + b = pt (r, c + 1) := fun r c => (hpt_b r c).symm
      have f2a : ∀ (r c : ZMod 3), pt (r, c) + 2 • a = pt (r + 2, c) := fun r c => by
        rw [show (2 : ZMod 3) = 1 + 1 by decide, ← add_assoc, hpt_a, hpt_a]; abel
      have f2b : ∀ (r c : ZMod 3), pt (r, c) + 2 • b = pt (r, c + 2) := fun r c => by
        rw [show (2 : ZMod 3) = 1 + 1 by decide, ← add_assoc, hpt_b, hpt_b]; abel
      rw [f, fb] at s1 s3; rw [f, f2a] at r0; rw [fb, f2b] at c0
      simp only [show (0 : ZMod 3) + 1 = 1 by decide, show (0 : ZMod 3) + 2 = 2 by decide,
        show (2 : ZMod 3) + 1 = 0 by decide] at s1 s3 r0 c0
      linear_combination (norm := abel) s3 - c0 + s1 - r0
    dsimp [hexV] at heq_12_20
    rw [← hpt_a 1 2, ← hpt_b 1 2, ← hpt_a 2 0, ← hpt_b 2 0] at heq_12_20
    simp only [show (0 : ZMod 3) + 1 = 1 by decide, show (1 : ZMod 3) + 1 = 2 by decide,
      show (2 : ZMod 3) + 1 = 0 by decide] at heq_12_20
    dsimp [g14, g13, g11, g15]
    linear_combination (norm := abel) heq_12_20 - hca2
  apply hno; apply hasPow2_of_16
  refine walk_to_cycle (by decide) (fun k => ((w k).1, pt (w k).2, gv k)) ?_ ?_
  · have hu_inj : Function.Injective (fun z : Bool × ZMod 3 × ZMod 3 => (z.1, pt z.2)) := by
      rintro ⟨s1, z1⟩ ⟨s2, z2⟩ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (hpt_inj h.2)
    refine walk_inj_of_cols (fun z : Bool × ZMod 3 × ZMod 3 => (z.1, pt z.2)) hu_inj w gv
      [(2, 12), (3, 11)] (by decide) ?_
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp [gv] <;> intro hg
    · exact hhex_nz (pt (1, 2)) (by have h12 : g12 = g11 := rfl; have h23 : g2 = g3 := rfl; linear_combination (norm := abel) -h_diff - hg + h12 - h23)
    · exact hhex_nz (pt (1, 2)) (by linear_combination (norm := abel) -h_diff - hg)
  · intro k; fin_cases k <;> dsimp [w, gv]
    · exact e0 (pt (0, 0)) g0
    · have h := ea_sub (a := a) (b := b) (x := x) (y := y) (pt (2, 0)) 0
      rw [← hpt_a, show (2 : ZMod 3) + 1 = 0 by decide, zero_sub] at h; exact h
    · exact e0 (pt (2, 0)) g2
    · have h := ea_sub (a := a) (b := b) (x := x) (y := y) (pt (1, 0)) g3
      rw [← hpt_a, show (1 : ZMod 3) + 1 = 2 by decide] at h; exact h
    · exact e0 (pt (1, 0)) g4
    · have h := eb_sub (a := a) (b := b) (x := x) (y := y) (pt (1, 2)) g5
      rw [← hpt_b, show (2 : ZMod 3) + 1 = 0 by decide] at h; exact h
    · exact e0 (pt (1, 2)) g6
    · have h := ea_sub (a := a) (b := b) (x := x) (y := y) (pt (0, 2)) g7
      rw [← hpt_a, show (0 : ZMod 3) + 1 = 1 by decide] at h; exact h
    · exact e0 (pt (0, 2)) g8
    · have h := ea_sub (a := a) (b := b) (x := x) (y := y) (pt (2, 2)) g9
      rw [← hpt_a, show (2 : ZMod 3) + 1 = 0 by decide] at h; exact h
    · have h := eb (a := a) (b := b) (x := x) (y := y) (pt (2, 2)) g10
      rw [← hpt_b, show (2 : ZMod 3) + 1 = 0 by decide] at h; exact h
    · exact e0' (pt (2, 0)) g11
    · have h := eb (a := a) (b := b) (x := x) (y := y) (pt (2, 0)) g12
      rw [← hpt_b, show (0 : ZMod 3) + 1 = 1 by decide] at h; exact h
    · exact e0' (pt (2, 1)) g13
    · have h := ea (a := a) (b := b) (x := x) (y := y) (pt (2, 1)) g14
      rw [← hpt_a, show (2 : ZMod 3) + 1 = 0 by decide, h_close] at h; exact h
    · have h := eb' (a := a) (b := b) (x := x) (y := y) (pt (0, 0)) 0
      rw [← hpt_b, show (0 : ZMod 3) + 1 = 1 by decide, zero_add] at h; exact h

/-- Complete proof of Case 3 (`3 • b = 0`, `a ∉ ⟨b⟩`, `2a ∉ ⟨b⟩`, `3a ≠ b`, `3a ≠ 2b`). -/
theorem case_3b_main (hb : b ≠ 0) (h3b : 3 • b = 0)
    (ha0 : a ≠ 0) (hab : a ≠ b) (ha2b : a ≠ 2 • b)
    (h2a0 : 2 • a ≠ 0) (h2ab : 2 • a ≠ b) (h2a2b : 2 • a ≠ 2 • b)
    (h3ab : 3 • a ≠ b) (h3a2b : 3 • a ≠ 2 • b) :
    HasPow2 (GNorm a b x y) := by
  by_contra hno
  -- Step 1: If all hexV = 0, done by hasPow2_of_all_hexV_zero!
  -- Otherwise pick i0 with hexV i0 ≠ 0.
  have hex : ∃ i0 : B, hexV a b x y i0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hno (hasPow2_of_all_hexV_zero ha0 hb hab hall)
  -- Helper: if hexV j ≠ 0, then cbV (j - a) = 0 (by case_3b_bar_CH)!
  have hbar : ∀ j : B, hexV a b x y j ≠ 0 → cbV b y (j - a) = 0 := by
    intro j hj
    by_contra hc
    exact hno (case_3b_bar_CH hb h3b ha0 hab ha2b h2a0 h2ab h2a2b (j - a) hc (by simpa using hj))
  -- Helper: if cbV j = 0, then hexV j ≠ 0 (by case_3b_c8)!
  have hc8 : ∀ j : B, cbV b y j = 0 → hexV a b x y j ≠ 0 := by
    intro j hj hh
    exact hno (case_3b_c8 hb h3b ha0 hab ha2b j (by rw [hh, hj, add_zero]))
  -- Therefore: if hexV j ≠ 0, then cbV (j - a) = 0, hence hexV (j - a) ≠ 0!
  -- By induction on n : ℕ, for all n, hexV (i0 - n•a) ≠ 0 and cbV (i0 - (n+1)•a) = 0!
  -- Wait: we only need `cbV = 0` and `hexV ≠ 0` at `i0`, `i0 - a`, `i0 - 2a` (and if 3a = 0, on all of Z/3 x Z/3!).
  obtain ⟨i0, hi0⟩ := hex
  have hcb_m1 : cbV b y (i0 - a) = 0 := hbar i0 hi0
  have hh_m1 : hexV a b x y (i0 - a) ≠ 0 := hc8 (i0 - a) hcb_m1
  have hcb_m2 : cbV b y (i0 - 2 • a) = 0 := by
    simpa [show i0 - a - a = i0 - 2 • a by abel] using hbar (i0 - a) hh_m1
  have hh_m2 : hexV a b x y (i0 - 2 • a) ≠ 0 := hc8 (i0 - 2 • a) hcb_m2
  by_cases h3a0 : 3 • a = 0
  · -- B' = <a, b> ≅ Z/3 x Z/3!
    -- Since 3a = 0, i0 - 3a = i0, so cbV = 0 on ALL of i0 + <a, b>, AND hexV ≠ 0 on ALL of i0 + <a, b>!
    -- Translate by i0 so 0 is i0!
    have hno' : ¬ HasPow2 (GNorm a b (fun j => x (j + i0)) (fun j => y (j + i0))) :=
      fun h => hno (hasPow2_mono (gnorm_translate i0) h)
    -- Wait: we can also prove cbV = 0 and hexV ≠ 0 on the whole subgroup <a, b>, OR even simpler:
    -- Since cbV_add_b holds, cbV (i0 - a + k*b) = 0, cbV (i0 - 2a + k*b) = 0, cbV (i0 - 3a + k*b) = cbV (i0 + k*b) = 0!
    -- Wait: in case_3b_z33 we only need `cbV`, `caV`, `hexV ≠ 0` on `B` — wait, `case_3b_z33` took `∀ i : B`!
    -- Because in `H1`, `AddSubgroup.closure {a, b} = ⊤`, EVERY `i : B` is in `<a, b>`!
    -- Better yet: pass `hgen : AddSubgroup.closure ({a, b} : Set B) = ⊤` to `case_3b_main` or prove `∀ i ∈ AddSubgroup.closure {a, b}`!
    -- Even cleaner: restrict to `B' = ZMod 3 × ZMod 3` by pulling back `x, y` along `pt : ZMod 3 × ZMod 3 → B` (shifted by `i0`)!
    let B3 := ZMod 3 × ZMod 3
    let a3 : B3 := (1, 0)
    let b3 : B3 := (0, 1)
    let pt : B3 → B := fun z => i0 + z.1.val • a + z.2.val • b
    have hpt_a : ∀ z : B3, pt (z + a3) = pt z + a := by
      rintro ⟨r, c⟩
      change pt (r + 1, c + 0) = pt (r, c) + a
      rw [add_zero]
      have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by revert r; decide
      rcases hr3 with rfl | rfl | rfl <;>
        simp only [pt, zero_add,
          show (1 : ZMod 3) + 1 = 2 by decide, show (2 : ZMod 3) + 1 = 0 by decide,
          ZMod.val_zero, ZMod.val_one, show (2 : ZMod 3).val = 2 by decide, zero_nsmul, one_nsmul]
      · abel
      · abel
      · linear_combination (norm := abel) -h3a0
    have hpt_b : ∀ z : B3, pt (z + b3) = pt z + b := by
      rintro ⟨r, c⟩
      change pt (r + 0, c + 1) = pt (r, c) + b
      rw [add_zero]
      have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide
      rcases hc3 with rfl | rfl | rfl <;>
        simp only [pt, zero_add,
          show (1 : ZMod 3) + 1 = 2 by decide, show (2 : ZMod 3) + 1 = 0 by decide,
          ZMod.val_zero, ZMod.val_one, show (2 : ZMod 3).val = 2 by decide, zero_nsmul, one_nsmul]
      · abel
      · abel
      · linear_combination (norm := abel) -h3b
    have h2b : 2 • b ≠ 0 := by intro e; exact hb (by linear_combination (norm := abel) h3b - e)
    have hpt_inj : Function.Injective pt := by
      rintro ⟨r1, c1⟩ ⟨r2, c2⟩ h
      by_contra hne
      have hsub : ((r1.val : ℤ) - (r2.val : ℤ)) • a + ((c1.val : ℤ) - (c2.val : ℤ)) • b = 0 := by
        dsimp [pt] at h; rw [sub_zsmul, sub_zsmul]; simp only [natCast_zsmul]; linear_combination (norm := abel) h
      have hr1 : r1.val < 3 := r1.val_lt; have hr2 : r2.val < 3 := r2.val_lt
      have hc1 : c1.val < 3 := c1.val_lt; have hc2 : c2.val < 3 := c2.val_lt
      have hne' : (r1.val : ℤ) - r2.val ≠ 0 ∨ ((c1.val : ℤ) - c2.val) % 3 ≠ 0 := by
        by_contra hall; push_neg at hall
        exact hne (Prod.ext (ZMod.val_injective 3 (by change r1.val = r2.val; omega)) (ZMod.val_injective 3 (by change c1.val = c2.val; omega)))
      exact ord3b_zsmul_ne hb h3b ha0 hab ha2b h2a0 h2ab h2a2b _ _ hne' (abs_le.mpr ⟨by omega, by omega⟩) (abs_le.mpr ⟨by omega, by omega⟩) hsub
    let x3 : B3 → V := fun z => x (pt z)
    let y3 : B3 → V := fun z => y (pt z)
    have hsub3 : GNorm a3 b3 x3 y3 ⊑ GNorm a b x y := by
      let emb : (Bool × B3 × V) ↪ (Bool × B × V) :=
        { toFun := fun z => (z.1, pt z.2.1, z.2.2)
          inj' := by
            rintro ⟨s1, i1, g1⟩ ⟨s2, i2, g2⟩ h
            simp only [Prod.mk.injEq] at h
            exact Prod.ext h.1 (Prod.ext (hpt_inj h.2.1) h.2.2) }
      refine ⟨⟨⟨emb, ?_⟩, emb.injective⟩⟩
      intro u v huv
      rcases huv with ⟨_, hr | hr⟩
      · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
        · exact e0 (pt i) g
        · change (GNorm a b x y).Adj (false, pt i, g) (true, pt (i + a3), g + x (pt i)); rw [hpt_a]; exact ea (pt i) g
        · change (GNorm a b x y).Adj (false, pt i, g) (true, pt (i + b3), g + y (pt i)); rw [hpt_b]; exact eb (pt i) g
      · rcases hr with ⟨i, g, rfl, rfl | rfl | rfl⟩
        · exact e0' (pt i) g
        · change (GNorm a b x y).Adj (true, pt (i + a3), g + x (pt i)) (false, pt i, g); rw [hpt_a]; exact ea' (pt i) g
        · change (GNorm a b x y).Adj (true, pt (i + b3), g + y (pt i)) (false, pt i, g); rw [hpt_b]; exact eb' (pt i) g
    have hno3 : ¬ HasPow2 (GNorm a3 b3 x3 y3) := fun h => hno (hasPow2_mono hsub3 h)
    have hcb_m3 : cbV b y i0 = 0 := by
      have := hbar (i0 - 2 • a) hh_m2
      have e : i0 - 2 • a - a = i0 := by linear_combination (norm := abel) -h3a0
      rwa [e] at this
    have hcb3 : ∀ z : B3, cbV b3 y3 z = 0 := by
      rintro ⟨r, c⟩
      have hcb_eq : cbV b3 y3 (r, c) = cbV b y (pt (r, c)) := by
        dsimp [cbV, y3]
        rw [hpt_b, show (2 : ℕ) • b3 = b3 + b3 by abel, ← add_assoc, hpt_b, hpt_b,
            show pt (r, c) + b + b = pt (r, c) + 2 • b by abel]
      rw [hcb_eq]
      have hshift_b : ∀ j : B, ∀ k : ZMod 3, cbV b y (j + k.val • b) = cbV b y j := by
        intro j k
        have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
        rcases hk3 with rfl | rfl | rfl
        · change cbV b y (j + (0 : ℕ) • b) = cbV b y j; simp
        · change cbV b y (j + (1 : ℕ) • b) = cbV b y j; simpa using cbV_add_b h3b j
        · change cbV b y (j + (2 : ℕ) • b) = cbV b y j
          rw [show (2 : ℕ) • b = b + b by abel, ← add_assoc, cbV_add_b h3b, cbV_add_b h3b]
      dsimp [pt]
      rw [hshift_b]
      have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by clear hcb_eq hshift_b; revert r; decide
      rcases hr3 with rfl | rfl | rfl
      · change cbV b y (i0 + (0 : ℕ) • a) = 0; simpa using hcb_m3
      · change cbV b y (i0 + (1 : ℕ) • a) = 0
        have e : i0 + (1 : ℕ) • a = i0 - 2 • a := by linear_combination (norm := abel) h3a0
        rwa [e]
      · change cbV b y (i0 + (2 : ℕ) • a) = 0
        have e : i0 + (2 : ℕ) • a = i0 - a := by linear_combination (norm := abel) h3a0
        rwa [e]
    have hhex3_nz : ∀ z : B3, hexV a3 b3 x3 y3 z ≠ 0 := by
      intro z hz
      exact hno3 (case_3b_c8 (by decide) (by decide) (by decide) (by decide) (by decide) z
        (by rw [hz, hcb3 z, add_zero]))
    have hca3 : ∀ z : B3, cbV a3 x3 z = 0 := by
      intro z
      have hno3_sw : ¬ HasPow2 (GNorm b3 a3 y3 x3) := fun h => hno3 (hasPow2_mono gnorm_swap_ab h)
      by_contra hc
      have hne : hexV b3 a3 y3 x3 (z + b3) ≠ 0 := by
        intro h0; exact hhex3_nz (z + b3) (by dsimp [hexV] at h0 ⊢; linear_combination (norm := abel) -h0)
      exact hno3_sw (case_3b_bar_CH (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) z hc hne)
    exact hno3 (case_3b_z33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hcb3 hca3 hhex3_nz)
  · -- 3a ≠ 0 (and 3a ≠ b, 3a ≠ 2b): horizontal barbell on H(i0 - 2a) and H(i0)!
    have hno' : ¬ HasPow2 (GNorm a b (fun j => x (j + (i0 - 2 • a))) (fun j => y (j + (i0 - 2 • a)))) :=
      fun h => hno (hasPow2_mono (gnorm_translate (i0 - 2 • a)) h)
    apply hno'
    apply case_3b_bar_2a hb h3b ha0 hab ha2b h2a0 h2ab h2a2b h3a0 h3ab h3a2b
    · simpa [hexV, add_comm] using hh_m2
    · have e1 : 2 • a + (i0 - 2 • a) = i0 := by abel
      have e2 : 2 • a + a + (i0 - 2 • a) = i0 + a := by abel
      have e3 : 2 • a + b + (i0 - 2 • a) = i0 + b := by abel
      simpa [hexV, e1, e2, e3] using hi0

end Case3bZero

/- ## Section 7: Master Dispatch and `OMA.solution` -/

section Master
variable {B V : Type*} [AddCommGroup B] [AddCommGroup V]

lemma case_a2b_z6 {a' b' : B} {x' y' : B → V}
    (hb' : b' ≠ 0) (ha2b' : a' = 2 • b')
    (h2b_nz : 2 • b' ≠ 0) (h3b' : 3 • b' ≠ 0) (h4b' : 4 • b' ≠ 0) (h5b' : 5 • b' ≠ 0) (h6b' : 6 • b' = 0) :
    HasPow2 (GNorm a' b' x' y') := by
  by_contra hno
  have hq5 : q2V b' x' y' (5 • b') ≠ 0 := fun h => hno (case_a2b_c4 hb' ha2b' h2b_nz (5 • b') h)
  have hq1 : q2V b' x' y' b' ≠ 0 := fun h => hno (case_a2b_c4 hb' ha2b' h2b_nz b' h)
  let u : Fin 11 → Bool × B := ![
    (true, 0), (false, 0), (true, b'), (false, 5 • b'),
    (false, 4 • b'), (true, 4 • b'), (false, 3 • b'),
    (true, 3 • b'), (false, b'), (true, 2 • b'), (false, 2 • b')]
  have hu : Function.Injective u := by
    intro p r hpr
    fin_cases p <;> fin_cases r <;> dsimp [u] at hpr
    all_goals first
      | rfl
      | (solve | exfalso; have h := congrArg Prod.fst hpr; simp at h)
      | (have e := congrArg Prod.snd hpr; dsimp at e
         first | (solve | exfalso; apply hb'; linear_combination (norm := abel) e)
               | (solve | exfalso; apply hb'; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h2b_nz; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h2b_nz; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h3b'; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h3b'; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h4b'; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h4b'; linear_combination (norm := abel) -e)
               | (solve | exfalso; apply h5b'; linear_combination (norm := abel) e)
               | (solve | exfalso; apply h5b'; linear_combination (norm := abel) -e))
  let g : Fin 11 → V := ![
    0, 0, y' 0, y' 0 - x' (5 • b'),
    -x' (4 • b'), -x' (4 • b'), -x' (4 • b') - y' (3 • b'),
    -x' (4 • b') - y' (3 • b'), -x' (4 • b') - y' (3 • b') - x' b',
    -x' (4 • b') - y' (3 • b') - x' b' + y' b',
    -x' (4 • b') - y' (3 • b') - x' b' + y' b']
  apply hno
  refine barbell_4_4_4 u hu g (q2V b' x' y' (5 • b')) (q2V b' x' y' b') hq5 hq1
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [u, g] using e0' (a := a') (b := b') (x := x') (y := y') 0 0
  · simpa [u, g, zero_add] using eb (a := a') (b := b') (x := x') (y := y') 0 0
  · have e1 : 5 • b' + a' = b' := by rw [ha2b']; linear_combination (norm := abel) h6b'
    dsimp [u, g]; have h := ea_sub (a := a') (b := b') (x := x') (y := y') (5 • b') (y' 0); rwa [e1] at h
  · have e1 : 5 • b' + b' = 0 := by linear_combination (norm := abel) h6b'
    have hv : y' 0 - x' (5 • b') + y' (5 • b') = 0 + q2V b' x' y' (5 • b') := by
      simp [q2V, e1]; abel
    dsimp [u, g]; have h := eb (a := a') (b := b') (x := x') (y := y') (5 • b') (y' 0 - x' (5 • b')); rwa [e1, hv] at h
  · have e1 : 4 • b' + a' = 0 := by rw [ha2b']; linear_combination (norm := abel) h6b'
    dsimp [u, g]; have h := ea_sub (a := a') (b := b') (x := x') (y := y') (4 • b') 0; rwa [e1, zero_sub] at h
  · dsimp [u, g]; exact e0 (4 • b') _
  · have e1 : 3 • b' + b' = 4 • b' := by abel
    dsimp [u, g]; have h := eb_sub (a := a') (b := b') (x := x') (y := y') (3 • b') (-x' (4 • b')); rwa [e1] at h
  · dsimp [u, g]; exact e0 (3 • b') _
  · have e1 : b' + a' = 3 • b' := by rw [ha2b']; abel
    dsimp [u, g]; have h := ea_sub (a := a') (b := b') (x := x') (y := y') b' (-x' (4 • b') - y' (3 • b')); rwa [e1] at h
  · have e1 : b' + b' = 2 • b' := by abel
    dsimp [u, g]; have h := eb (a := a') (b := b') (x := x') (y := y') b' (-x' (4 • b') - y' (3 • b') - x' b'); rwa [e1] at h
  · dsimp [u, g]; exact e0' (2 • b') _
  · have e1 : 2 • b' + b' = 3 • b' := by abel
    have f1 : b' + b' = 2 • b' := by abel
    have hv : -x' (4 • b') - y' (3 • b') - x' b' + y' b' + y' (2 • b') =
        -x' (4 • b') - y' (3 • b') + q2V b' x' y' b' := by simp [q2V, f1]; abel
    dsimp [u, g]; have h := eb (a := a') (b := b') (x := x') (y := y') (2 • b') (-x' (4 • b') - y' (3 • b') - x' b' + y' b'); rwa [e1, hv] at h

/-- Master theorem for `GNorm`: works for EVERY `[Finite B]` and `a ≠ 0, b ≠ 0, a ≠ b`! -/
theorem gnorm_hasPow2 [Finite B] (a b : B) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (x y : B → V) : HasPow2 (GNorm a b x y) := by
  -- Helper: apply any theorem after swap_ab or swap_0a
  have via_ab : HasPow2 (GNorm b a y x) → HasPow2 (GNorm a b x y) := hasPow2_mono gnorm_swap_ab
  have via_0a : HasPow2 (GNorm (-a) (b - a) (fun i => -x (i - a)) (fun i => y i - x (i + b - a))) →
      HasPow2 (GNorm a b x y) := hasPow2_mono gnorm_swap_0a
  have via_0b : HasPow2 (GNorm (-b) (a - b) (fun i => -y (i - b)) (fun i => x i - y (i + a - b))) →
      HasPow2 (GNorm a b x y) := fun h => via_ab (hasPow2_mono gnorm_swap_0a h)
  -- Orbit 1: 2a = 0 ∨ 2b = 0 ∨ 2(a - b) = 0
  by_cases h2b : b + b = 0
  · exact case_2b_zero ha hb hab h2b
  by_cases h2a : a + a = 0
  · exact via_ab (case_2b_zero hb ha hab.symm h2a)
  by_cases h2ab : (a - b) + (a - b) = 0
  · exact via_0b (case_2b_zero (neg_ne_zero.mpr hb) (sub_ne_zero.mpr hab)
      (by intro e; exact ha (by linear_combination (norm := abel) -e)) h2ab)
  -- Helper: dispatch `a = 2 • b` (when Orbit 1 is already false!)
  have solve_a2b : ∀ {a' b' : B} {x' y' : B → V},
      a' ≠ 0 → b' ≠ 0 → a' ≠ b' → a' + a' ≠ 0 → b' + b' ≠ 0 → (a' - b') + (a' - b') ≠ 0 →
      a' = 2 • b' → HasPow2 (GNorm a' b' x' y') := by
    intro a' b' x' y' ha' hb' hab' h2a' h2b' _ ha2b'
    have h2b_nz : 2 • b' ≠ 0 := by intro e; exact h2b' (by linear_combination (norm := abel) e)
    by_cases h3b' : 3 • b' = 0
    · exact case_a2b_k33 hb' ha2b' h3b'
    by_cases h4b' : 4 • b' = 0
    · exfalso; exact h2a' (by rw [ha2b']; linear_combination (norm := abel) h4b')
    by_cases h5b' : 5 • b' = 0
    · exact case_a2b_z5 hb' ha2b' h5b'
    by_cases h6b' : 6 • b' = 0
    · exact case_a2b_z6 hb' ha2b' h2b_nz h3b' h4b' h5b' h6b'
    · exact case_a2b_ge7 hb' ha2b' h2b_nz h3b' h4b' h5b' h6b'
  -- Orbit 2: a = 2b ∨ b = 2a ∨ a + b = 0
  by_cases ha2b : a = 2 • b
  · exact solve_a2b ha hb hab h2a h2b h2ab ha2b
  by_cases hb2a : b = 2 • a
  · exact via_ab (solve_a2b hb ha hab.symm h2b h2a (by intro e; exact h2ab (by linear_combination (norm := abel) -e)) hb2a)
  by_cases hab0 : a + b = 0
  · exact via_0a (hasPow2_mono gnorm_swap_ab (solve_a2b (sub_ne_zero.mpr hab.symm) (neg_ne_zero.mpr ha)
      (by intro e; exact hb (by linear_combination (norm := abel) e))
      (by intro e; exact h2ab (by linear_combination (norm := abel) -e))
      (by intro e; exact h2a (by linear_combination (norm := abel) -e))
      (by intro e; exact h2b (by linear_combination (norm := abel) e))
      (by linear_combination (norm := abel) hab0)))
  -- Helper: dispatch `a = 3 • b` (when Orbits 1 & 2 are already false!)
  have solve_a3b : ∀ {a' b' : B} {x' y' : B → V},
      a' ≠ 0 → b' ≠ 0 → a' ≠ b' →
      a' + a' ≠ 0 → b' + b' ≠ 0 → (a' - b') + (a' - b') ≠ 0 →
      a' ≠ 2 • b' → b' ≠ 2 • a' → a' + b' ≠ 0 →
      a' = 3 • b' → HasPow2 (GNorm a' b' x' y') := by
    intro a' b' x' y' ha' hb' hab' h2a' h2b' _ _ hb2a' hab0' ha3b'
    have h2b_nz : 2 • b' ≠ 0 := by intro e; exact h2b' (by linear_combination (norm := abel) e)
    have h3b_nz : 3 • b' ≠ 0 := by rwa [← ha3b']
    have h4b_nz : 4 • b' ≠ 0 := by
      intro e; exact hab0' (by rw [ha3b']; linear_combination (norm := abel) e)
    have h5b_nz : 5 • b' ≠ 0 := by
      intro e; exact hb2a' (by rw [ha3b']; linear_combination (norm := abel) -e)
    have h6b_nz : 6 • b' ≠ 0 := by
      intro e; exact h2a' (by rw [ha3b']; linear_combination (norm := abel) e)
    exact case_a3b_ge7 ha3b' hb' h2b_nz h3b_nz h4b_nz h5b_nz h6b_nz
  -- Orbit 4: a = 3b ∨ b = 3a ∨ a + 2b = 0 ∨ 2a + b = 0 ∨ 3a = 2b ∨ 2a = 3b
  by_cases ha3b : a = 3 • b
  · exact solve_a3b ha hb hab h2a h2b h2ab ha2b hb2a hab0 ha3b
  by_cases hb3a : b = 3 • a
  · exact via_ab (solve_a3b hb ha hab.symm h2b h2a (by intro e; exact h2ab (by linear_combination (norm := abel) -e))
      hb2a ha2b (by rw [add_comm]; exact hab0) hb3a)
  by_cases ha2b0 : a + 2 • b = 0
  · exact via_0b (hasPow2_mono gnorm_swap_ab (solve_a3b (sub_ne_zero.mpr hab) (neg_ne_zero.mpr hb)
      (by intro e; exact ha (by linear_combination (norm := abel) e))
      h2ab (by intro e; exact h2b (by linear_combination (norm := abel) -e))
      (by intro e; exact h2a (by linear_combination (norm := abel) e))
      (by intro e; exact hab0 (by linear_combination (norm := abel) e))
      (by intro e; exact hb2a (by linear_combination (norm := abel) e))
      (by intro e; exact ha2b (by linear_combination (norm := abel) e))
      (by linear_combination (norm := abel) ha2b0)))
  by_cases h2ab0 : 2 • a + b = 0
  · exact via_0a (hasPow2_mono gnorm_swap_ab (solve_a3b (sub_ne_zero.mpr hab.symm) (neg_ne_zero.mpr ha)
      (by intro e; exact hb (by linear_combination (norm := abel) e))
      (by intro e; exact h2ab (by linear_combination (norm := abel) -e))
      (by intro e; exact h2a (by linear_combination (norm := abel) -e))
      (by intro e; exact h2b (by linear_combination (norm := abel) e))
      (by intro e; exact hab0 (by linear_combination (norm := abel) e))
      (by intro e; exact ha2b (by linear_combination (norm := abel) e))
      (by intro e; exact hb2a (by linear_combination (norm := abel) e))
      (by linear_combination (norm := abel) h2ab0)))
  by_cases h3a2b : 3 • a = 2 • b
  · exact via_0b (solve_a3b (neg_ne_zero.mpr hb) (sub_ne_zero.mpr hab)
      (by intro e; exact ha (by linear_combination (norm := abel) -e))
      (by intro e; exact h2b (by linear_combination (norm := abel) -e)) h2ab
      (by intro e; exact h2a (by linear_combination (norm := abel) -e))
      (by intro e; exact hb2a (by linear_combination (norm := abel) e))
      (by intro e; exact hab0 (by linear_combination (norm := abel) e))
      (by intro e; exact ha2b (by linear_combination (norm := abel) e))
      (by linear_combination (norm := abel) -h3a2b))
  by_cases h2a3b : 2 • a = 3 • b
  · exact via_0a (solve_a3b (neg_ne_zero.mpr ha) (sub_ne_zero.mpr hab.symm)
      (by intro e; exact hb (by linear_combination (norm := abel) -e))
      (by intro e; exact h2a (by linear_combination (norm := abel) -e))
      (by intro e; exact h2ab (by linear_combination (norm := abel) -e))
      (by intro e; exact h2b (by linear_combination (norm := abel) -e))
      (by intro e; exact ha2b (by linear_combination (norm := abel) e))
      (by intro e; exact hab0 (by linear_combination (norm := abel) e))
      (by intro e; exact hb2a (by linear_combination (norm := abel) e))
      (by linear_combination (norm := abel) h2a3b))
  -- Orbit 3: 3b = 0 ∨ 3a = 0 ∨ 3(a - b) = 0 (when Orbits 1, 2, 4 are ALL false!)
  by_cases h3b : 3 • b = 0
  · exact case_3b_main hb h3b ha hab ha2b
      (by intro e; exact h2a (by linear_combination (norm := abel) e))
      (by intro e; exact hb2a e.symm)
      (by intro e; exact h2ab (by linear_combination (norm := abel) e))
      (by intro e; exact hb3a e.symm) h3a2b
  by_cases h3a : 3 • a = 0
  · exact via_ab (case_3b_main ha h3a hb hab.symm hb2a
      (by intro e; exact h2b (by linear_combination (norm := abel) e))
      (by intro e; exact ha2b e.symm)
      (by intro e; exact h2ab (by linear_combination (norm := abel) -e))
      (by intro e; exact ha3b e.symm) (Ne.symm h2a3b))
  by_cases h3ab : 3 • (a - b) = 0
  · exact via_0b (case_3b_main (sub_ne_zero.mpr hab) h3ab (neg_ne_zero.mpr hb)
      (by intro e; exact ha (by linear_combination (norm := abel) -e))
      (by intro e; exact hb2a (by linear_combination (norm := abel) e))
      (by intro e; exact h2b (by linear_combination (norm := abel) -e))
      (by intro e; exact hab0 (by linear_combination (norm := abel) -e))
      (by intro e; exact h2a (by linear_combination (norm := abel) -e))
      (by intro e; exact ha2b0 (by linear_combination (norm := abel) -e))
      (by intro e; exact h2ab0 (by linear_combination (norm := abel) -e)))
  -- General Case (Case 5)!
  exact general_case ⟨ha, hb, hab, h2a, h2b, h2ab, h3a, h3b, h3ab, ha2b, hb2a, hab0,
    ha3b, hb3a, ha2b0, h2ab0, h3a2b, h2a3b⟩

end Master

end Erdos64H1Proof

theorem OMA.solution :
    OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1.H1 := by
  intro B _ _ a b ha hb hab _ V _ w
  exact Erdos64H1Proof.hasPow2_mono (Erdos64H1Proof.gnorm_le_orig a b w)
    (Erdos64H1Proof.gnorm_hasPow2 a b ha hb hab _ _)

