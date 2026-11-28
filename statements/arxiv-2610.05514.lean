import Mathlib

namespace OMA.S_arxiv_2610_05514

open scoped Classical

section Geometry

variable (F K : Type*) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

/-- A line of the regular spread of `PG(3, q)` modeled by `V = K × K` over `F = GF(q)`:
`none` represents `J(∞) = {(0, x) : x ∈ K}`, and `some k` represents `J(k) = {(x, k * x) : x ∈ K}`. -/
def spreadLine (k : Option K) : Submodule F (K × K) where
  carrier :=
    match k with
    | none => {p : K × K | p.1 = 0}
    | some c => {p : K × K | p.2 = c * p.1}
  add_mem' := by
    intro p q hp hq
    cases k with
    | none => change p.1 + q.1 = 0; change p.1 = 0 at hp; change q.1 = 0 at hq; rw [hp, hq, add_zero]
    | some c =>
      change p.2 + q.2 = c * (p.1 + q.1)
      change p.2 = c * p.1 at hp; change q.2 = c * q.1 at hq
      rw [hp, hq, mul_add]
  zero_mem' := by
    cases k <;> simp
  smul_mem' := by
    intro r p hp
    cases k with
    | none =>
      change r • p.1 = 0
      change p.1 = 0 at hp
      rw [hp, smul_zero]
    | some c =>
      change r • p.2 = c * (r • p.1)
      change p.2 = c * p.1 at hp
      rw [hp, Algebra.smul_def, Algebra.smul_def]
      ring

/-- The Miquelian circle `C(λ, a, b)` in `M(q) = K ∪ {∞}`, consisting of all `x ∈ K` satisfying
`b x^(q+1) - λ^q x - λ x^q - a = 0`, together with `∞` (`none`) when `b = 0`. -/
noncomputable def miquelianCircle (lam : K) (a b : F) : Finset (Option K) :=
  let q := Fintype.card F
  Finset.univ.filter fun k =>
    match k with
    | none => b = 0
    | some x =>
      algebraMap F K b * (x * x ^ q) - lam ^ q * x - lam * x ^ q - algebraMap F K a = 0

/-- Non-degeneracy predicate for a Miquelian circle `C(λ, a, b)`: `λ^(q+1) + a * b ≠ 0`. -/
def IsMiquelianCircle (C : Finset (Option K)) : Prop :=
  let q := Fintype.card F
  ∃ (lam : K) (a b : F),
    lam * lam ^ q + algebraMap F K (a * b) ≠ 0 ∧ C = miquelianCircle F K lam a b

/-- A projective line `L` of `PG(3, q)` (a 2-dimensional `F`-subspace of `K × K`) lies in the
opposite regulus of the regulus corresponding to `C` if it meets every spread line in `C`. -/
def IsOppositeLine (C : Finset (Option K)) (L : Submodule F (K × K)) : Prop :=
  Module.finrank F L = 2 ∧ ∀ k ∈ C, L ⊓ spreadLine F K k ≠ ⊥

/-- A `t`-nest in the regular spread of `PG(3, q)` is a collection `N` of `t` Miquelian circles
(reguli in the regular spread) such that every spread line lies in either `0` or `2` of them. -/
def IsNest (t : ℕ) (N : Finset (Finset (Option K))) : Prop :=
  N.card = t ∧
  (∀ C ∈ N, IsMiquelianCircle F K C) ∧
  (∀ k : Option K,
    (N.filter (fun C => k ∈ C)).card = 0 ∨ (N.filter (fun C => k ∈ C)).card = 2)

/-- A nest `N` is hemi-replaceable if one can select `(q + 1) / 2` opposite-regulus lines for each
regulus `C ∈ N` such that all chosen lines across `N` are pairwise disjoint in `PG(3, q)`. -/
def IsHemiReplaceable (N : Finset (Finset (Option K))) : Prop :=
  let q := Fintype.card F
  ∃ H : Finset (Option K) → Finset (Submodule F (K × K)),
    (∀ C ∈ N, (H C).card = (q + 1) / 2 ∧ ∀ L ∈ H C, IsOppositeLine F K C L) ∧
    (∀ C₁ ∈ N, ∀ L₁ ∈ H C₁, ∀ C₂ ∈ N, ∀ L₂ ∈ H C₂,
      (C₁ ≠ C₂ ∨ L₁ ≠ L₂) → L₁ ⊓ L₂ = ⊥)

/-- The action of a scalar `γ ∈ K` on `K × K` by `(x, y) ↦ (γ * x, γ * y)`, viewed as an
`F`-linear map (used to define the Bruck kernel map `Ψ` when `γ` is a primitive element of `Kˣ`). -/
def bruckKernelMap (γ : K) : (K × K) →ₗ[F] (K × K) where
  toFun p := (γ * p.1, γ * p.2)
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' r p := by
    ext <;> simp [Algebra.smul_def] <;> ring

/-- A nest `N` is Bruck replaceable if it is hemi-replaceable with each opposite half-regulus
`H C` being an orbit under `Ψ²`, the square of the Bruck kernel map for a primitive element `β`
of `Kˣ`. -/
def IsBruckReplaceable (N : Finset (Finset (Option K))) : Prop :=
  let q := Fintype.card F
  ∃ (β : Kˣ), (∀ x : Kˣ, x ∈ Subgroup.zpowers β) ∧
    ∃ H : Finset (Option K) → Finset (Submodule F (K × K)),
      (∀ C ∈ N, (H C).card = (q + 1) / 2 ∧
        (∀ L ∈ H C, IsOppositeLine F K C L) ∧
        (∃ L₀ ∈ H C, ∀ L, L ∈ H C ↔ ∃ j : ℕ, L = L₀.map (bruckKernelMap F K ((β : K) ^ (2 * j))))) ∧
      (∀ C₁ ∈ N, ∀ L₁ ∈ H C₁, ∀ C₂ ∈ N, ∀ L₂ ∈ H C₂,
        (C₁ ≠ C₂ ∨ L₁ ≠ L₂) → L₁ ⊓ L₂ = ⊥)

/-- Action of a nonzero scalar `d ∈ Fˣ` on `M(q) = K ∪ {∞}` by `x ↦ d * x` (fixing `0` and `∞`). -/
def scaleOption (d : Fˣ) : Option K → Option K
  | none => none
  | some x => some (algebraMap F K (d : F) * x)

/-- The orbit of a circle `D` under the cyclic group `H = Fˣ` acting by `x ↦ d * x`. -/
noncomputable def bundleOrbit (D : Finset (Option K)) : Finset (Finset (Option K)) :=
  (Finset.univ : Finset Fˣ).image (fun d => D.image (scaleOption F K d))

end Geometry

theorem main :
    (∀ (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K],
      Odd (Fintype.card F) →
      Fintype.card K = Fintype.card F ^ 2 →
      ∀ b : F, IsSquare (b * (b + 1)) → b * (b + 1) ≠ 0 →
        let q := Fintype.card F
        let D := miquelianCircle F K 1 1 b
        let N := bundleOrbit F K D
        IsNest F K (q - 1) N ∧
        IsBruckReplaceable F K N ∧
        ∃ D' : Finset (Option K),
          let N' := bundleOrbit F K D'
          IsNest F K (q - 1) N' ∧
          IsBruckReplaceable F K N' ∧
          (∀ C ∈ N, ∀ C' ∈ N', Disjoint C C')) ∧
    (∃ (F K : Type) (_ : Field F) (_ : Fintype F) (_ : Field K) (_ : Fintype K)
      (_ : Algebra F K),
      Fintype.card F = 9 ∧
      Fintype.card K = 81 ∧
      ∃ (t : ℕ) (N : Finset (Finset (Option K))),
        t ≤ Fintype.card F ∧
        IsNest F K t N ∧
        ¬ IsHemiReplaceable F K N) := by
  sorry

end OMA.S_arxiv_2610_05514
