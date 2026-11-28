import Mathlib

namespace OMA.S_arxiv_2608_18006

/-- Homogeneity of a configuration matrix `A ∈ ℤ^{d × n}`: its columns lie in an affine
hyperplane not containing the origin (`∃ h ∈ ℚ^d, h^T A = (1, ..., 1)`). -/
def IsHomogeneousConfig {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℤ) : Prop :=
  ∃ h : Fin d → ℚ, ∀ j : Fin n, ∑ i : Fin d, h i * (A i j : ℚ) = 1

/-- The columns of `B ∈ ℤ^{n × r}` form a `ℤ`-basis of the integer kernel `L = ker_ℤ(A)`,
so the lattice rank is `r`. -/
def HasLatticeBasis {d n r : ℕ} (A : Matrix (Fin d) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin r) ℤ) : Prop :=
  (∀ z : Fin r → ℤ, A.mulVec (B.mulVec z) = 0) ∧
  (∀ u : Fin n → ℤ, A.mulVec u = 0 → ∃! z : Fin r → ℤ, B.mulVec z = u)

/-- A weight vector `w ∈ ℝ^n` is generic for the lattice `L = im_ℤ(B)` if `w · u ≠ 0`
for every nonzero `u ∈ L`. -/
def IsGenericWeight {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℤ) (w : Fin n → ℝ) : Prop :=
  ∀ z : Fin r → ℤ, z ≠ 0 → ∑ j : Fin n, w j * ((B.mulVec z j : ℤ) : ℝ) ≠ 0

/-- An integer vector `v ∈ ℤ^n` is a fake exponent in direction `w` if it annihilates the
distraction of every initial monomial `∂^{u_+}` of the toric ideal `I_A` (`u ∈ L`, `w · u > 0`),
i.e. some coordinate `j` satisfies `0 ≤ v_j < u_j`. -/
def IsFakeExponent {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℤ) (w : Fin n → ℝ)
    (v : Fin n → ℤ) : Prop :=
  ∀ z : Fin r → ℤ,
    0 < ∑ j : Fin n, w j * ((B.mulVec z j : ℤ) : ℝ) →
    ∃ j : Fin n, 0 ≤ v j ∧ v j < B.mulVec z j

/-- Negative support `nsupp(x) = {j | x_j < 0}` of an integer vector `x ∈ ℤ^n`. -/
def nsupp {n : ℕ} (x : Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j < 0)

/-- The set `𝒮(v) = {nsupp(v + u) | u ∈ L}` of all negative supports realized by lattice shifts. -/
def realizedSupports {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℤ) (v : Fin n → ℤ) :
    Set (Finset (Fin n)) :=
  { I | ∃ z : Fin r → ℤ, nsupp (fun j => v j + B.mulVec z j) = I }

/-- The distinguished collection `𝒩_v` of all realized negative supports whose support fibers
consist entirely of lattice shifts of nonnegative `w`-weight. -/
def distinguishedCollection {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℤ) (w : Fin n → ℝ)
    (v : Fin n → ℤ) : Set (Finset (Fin n)) :=
  { I | I ∈ realizedSupports B v ∧
        ∀ z : Fin r → ℤ, nsupp (fun j => v j + B.mulVec z j) = I →
          0 ≤ ∑ j : Fin n, w j * ((B.mulVec z j : ℤ) : ℝ) }

/-- An ordered negative support family `𝒩` for `(B, w, v)` satisfies `nsupp(v) ∈ 𝒩 ⊆ 𝒩_v`
and is downward-closed inside `𝒮(v)`. -/
def IsOrderedNegSupportFamily {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℤ) (w : Fin n → ℝ)
    (v : Fin n → ℤ) (N : Set (Finset (Fin n))) : Prop :=
  nsupp v ∈ N ∧ N ⊆ distinguishedCollection B w v ∧
  ∀ I ∈ N, ∀ J ∈ realizedSupports B v, J ⊆ I → J ∈ N

/-- Common intersection `K_𝒩 = ⋂_{I ∈ 𝒩} I`. -/
noncomputable def commonNegSupport {n : ℕ} (N : Set (Finset (Fin n))) : Finset (Fin n) :=
  open Classical in Finset.univ.filter (fun j => ∀ I ∈ N, j ∈ I)

/-- Squarefree monomial `t^S = ∏_{j ∈ S} t_j` in `ℂ[t_1, ..., t_n]`. -/
noncomputable def monom {n : ℕ} (S : Finset (Fin n)) : MvPolynomial (Fin n) ℂ :=
  ∏ j ∈ S, MvPolynomial.X j

/-- Linear Euler ideal `U = ⟨A t⟩ ⊆ ℂ[t_1, ..., t_n]`. -/
noncomputable def eulerIdeal {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℤ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range (fun i : Fin d => ∑ j : Fin n, (A i j : ℂ) • MvPolynomial.X j))

/-- Monomial support ideal `M_𝒩 = ⟨t^{I \ K_𝒩} | I ∈ 𝒩⟩ ⊆ ℂ[t_1, ..., t_n]`. -/
noncomputable def supportIdeal {n : ℕ} (N : Set (Finset (Fin n))) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span { p | ∃ I ∈ N, p = monom (I \ commonNegSupport N) }

/-- Monomial boundary ideal `P_𝒩(t) = ⟨t^{(I ∪ J) \ K_𝒩} | I ∈ 𝒩, J ∈ 𝒮(v) \ 𝒩⟩`. -/
noncomputable def boundaryIdeal {n r : ℕ} (B : Matrix (Fin n) (Fin r) ℤ) (v : Fin n → ℤ)
    (N : Set (Finset (Fin n))) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span { p | ∃ I ∈ N, ∃ J ∈ realizedSupports B v, J ∉ N ∧
    p = monom ((I ∪ J) \ commonNegSupport N) }

/-- Nonvanishing of the intrinsic-perturbation obstruction module
`𝔇_𝒩(e) = ((U + P_𝒩) : e) / ((U M_𝒩 + P_𝒩) : e)` for `e = t^{nsupp(v) \ K_𝒩}`:
there exists `f ∈ ℂ[t_1, ..., t_n]` with `e * f ∈ U + P_𝒩` and `e * f ∉ U M_𝒩 + P_𝒩`. -/
def HasNonzeroObstruction {d n r : ℕ} (A : Matrix (Fin d) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin r) ℤ) (v : Fin n → ℤ) (N : Set (Finset (Fin n))) : Prop :=
  let e := monom (nsupp v \ commonNegSupport N);
  let U := eulerIdeal A;
  let M := supportIdeal N;
  let P := boundaryIdeal B v N;
  ∃ f : MvPolynomial (Fin n) ℂ, e * f ∈ U + P ∧ e * f ∉ U * M + P

/-- Existence of homogeneous `A`-hypergeometric configurations of lattice rank 1 and 2
with nonzero intrinsic-perturbation obstruction (arXiv:2608.18006, Theorems 6.1 and 6.10),
including a rank-2 configuration whose distinguished collection `𝒩_v` is itself ordered,
settling Okuyama–Saito's Question 7.3. -/
theorem main :
    (∃ (d n : ℕ) (A : Matrix (Fin d) (Fin n) ℤ) (B : Matrix (Fin n) (Fin 1) ℤ)
      (w : Fin n → ℝ) (v : Fin n → ℤ) (N : Set (Finset (Fin n))),
      IsHomogeneousConfig A ∧
      HasLatticeBasis A B ∧
      IsGenericWeight B w ∧
      IsFakeExponent B w v ∧
      IsOrderedNegSupportFamily B w v N ∧
      HasNonzeroObstruction A B v N) ∧
    (∃ (d n : ℕ) (A : Matrix (Fin d) (Fin n) ℤ) (B : Matrix (Fin n) (Fin 2) ℤ)
      (w : Fin n → ℝ) (v : Fin n → ℤ),
      IsHomogeneousConfig A ∧
      HasLatticeBasis A B ∧
      IsGenericWeight B w ∧
      IsFakeExponent B w v ∧
      IsOrderedNegSupportFamily B w v (distinguishedCollection B w v) ∧
      HasNonzeroObstruction A B v (distinguishedCollection B w v)) := by sorry

end OMA.S_arxiv_2608_18006
