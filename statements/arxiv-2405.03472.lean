import Mathlib

/-!
# Conjecture 1 of Katona, Wang, Wibisono: conservation of the truncated modified Hamiltonian

Source: https://arxiv.org/abs/2405.03472 (Katona, Wang, Wibisono, A Symplectic Analysis of
Alternating Mirror Descent; v4 of 17 November 2025; JMLR 27(44), 2026), Section 7, Conjecture 1.
Credit: @tatashbar

The source (Conjecture 1, in words). If P, Q are closed convex subsets of R^d and F : P → R,
G : Q → R are both L-smooth of orders 1, ..., N+2, then for symplectic Euler (5) with any stepsize
η > 0,
  |H^(N)_η(z_k) - H^(N)_η(z_0)| ≤ k Φ(N) L^(N+3) η^(N+2)        (22)
holds for each N in N_0 and some monotonic increasing, bounded function Φ : N_0 → Q.

Definitions of the source used here.
* L-smooth of order k (Section 2.1): k times continuously differentiable with operator norm of the
  k-th derivative at most L at every point.
* Symplectic Euler (5): p_{k+1} = p_k - η ∇G(q_k), q_{k+1} = q_k + η ∇F(p_{k+1}).
* Poisson bracket (Section 6): {φ, ψ} = -∇_p φ · ∇_q ψ + ∇_q φ · ∇_p ψ.
* Corrections H_n (Definition 3, equation (21)):
  H_n = 1/(n+1) * Σ_{m=1}^{n+1} (-1)^(m-1)/m * Σ {G^r1 F^s1 ... G^rm F^sm} / Π r_i! s_i!,
  the inner sum over all (r_i, s_i) with r_i + s_i > 0 and Σ (r_i + s_i) = n + 1;
  H^(N)_η = Σ_{j ≤ N} η^j H_j.

Status. The regret consequence of the conjecture is superseded by Nan and Kroer, arXiv 2611.05243.
The statement below is believed FALSE: for d = 1, P = Q = (-∞, 0], F = exp, G = exp, the constant
must grow at least geometrically (computer-assisted proof of 27 November 2026, read independently by a
second AI session, not read by a human; a Lean refutation of this statement is written and will be
filed once the statement is merged). It is stated because it is what the source states. The same
question for P = Q = R^d is not settled.

Formalization choices, and where a reader could object.
1. Order of quantifiers. Φ is taken universal (one Φ for all d, P, Q, F, G, L, η). The source
   introduces Φ at the end of the sentence, but tabulates it as a fixed function (Appendix G) and
   uses a universal upper bound on it in the proof of Theorem 4. The weaker reading (Φ depending on
   F, G, η) is refuted by the same example.
2. The iterated bracket of a word. Equation (21) writes {G^r1 F^s1 ... G^rm F^sm}. Following
   Appendix B.1 of the source (the Dynkin bracket [x,[x,...[y,...]]] with the arguments of the
   Poisson bracket swapped, that is, in reverse order), the word a_1 a_2 ... a_l is read as
   {...{{a_l, a_(l-1)}, a_(l-2)}, ..., a_1}. This is the reading that reproduces the expansion
   displayed in Section 7 of the source: H_1 = (1/2){F,G}, H_2 = (1/12)({{F,G},G} + {{G,F},F}),
   H_3 = -(1/24){{{F,G},G},F}. Reading the word from left to right instead changes the sign of H_n
   for odd n and contradicts that display.
3. Functions on closed sets. F and G are total functions on R^d; all derivatives are taken within
   P, within Q, or within P × Q (gradientWithin, iteratedFDerivWithin). To make these derivatives
   unique, P and Q are assumed to have nonempty interior (Section 3 of the source takes P and Q
   closed with nonempty interiors; the conjecture itself only says closed and convex).
4. The iterates z_0, ..., z_k are assumed to lie in P × Q (the source does not say what happens if
   an iterate leaves the domain). This is the reading under which the statement was refereed: the
   conjecture for closed convex domains and orbit segments that remain in them. The proof of
   Lemma 18 of the source (Appendix F) is written for iterates that remain in P × Q.
5. Operator norm. Mathlib's norm of the k-th derivative is the supremum over all k-tuples of unit
   vectors; the source bounds the diagonal values on unit vectors. For symmetric multilinear forms
   on a Euclidean space the two agree.
6. Monotonic increasing is read as Monotone (not strictly increasing). L is assumed positive.
-/

namespace OMA.S_arxiv_2405_03472

open scoped BigOperators

/-- The space R^d with its Euclidean norm. -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- `f` is `L`-smooth of orders `1, ..., m` on the set `S`. -/
def LSmoothUpTo {d : ℕ} (f : E d → ℝ) (S : Set (E d)) (L : ℝ) (m : ℕ) : Prop :=
  ContDiffOn ℝ m f S ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ m → ∀ x ∈ S, ‖iteratedFDerivWithin ℝ k f S x‖ ≤ L

/-- The Poisson bracket of the source on `P × Q`:
`{φ, ψ} = -∇_p φ · ∇_q ψ + ∇_q φ · ∇_p ψ`. -/
noncomputable def pb {d : ℕ} (P Q : Set (E d)) (φ ψ : E d × E d → ℝ) : E d × E d → ℝ := fun z =>
  -(inner ℝ (gradientWithin (fun p => φ (p, z.2)) P z.1)
        (gradientWithin (fun q => ψ (z.1, q)) Q z.2))
    + inner ℝ (gradientWithin (fun q => φ (z.1, q)) Q z.2)
        (gradientWithin (fun p => ψ (p, z.2)) P z.1)

/-- The letters of a word: `true` stands for `G` (a function of `q`), `false` for `F` (a function
of `p`). -/
def letter {d : ℕ} (F G : E d → ℝ) : Bool → (E d × E d → ℝ)
  | true => fun z => G z.2
  | false => fun z => F z.1

/-- The iterated Poisson bracket of a word `a_1 a_2 ... a_l`, read as
`{...{{a_l, a_(l-1)}, a_(l-2)}, ..., a_1}` (choice 2 in the header). A single letter is the
function itself. -/
noncomputable def ipb {d : ℕ} (P Q : Set (E d)) (F G : E d → ℝ) : List Bool → (E d × E d → ℝ)
  | [] => fun _ => 0
  | [a] => letter F G a
  | a :: b :: w => pb P Q (ipb P Q F G (b :: w)) (letter F G a)

/-- The word `G^(r 0) F^(s 0) G^(r 1) F^(s 1) ...`. -/
def word {m : ℕ} (rs : Fin m → ℕ × ℕ) : List Bool :=
  (List.ofFn fun i => List.replicate (rs i).1 true ++ List.replicate (rs i).2 false).flatten

/-- The `n`-th correction `H_n` of the modified Hamiltonian (Definition 3, equation (21)). -/
noncomputable def corr {d : ℕ} (P Q : Set (E d)) (F G : E d → ℝ) (n : ℕ) : E d × E d → ℝ := fun z =>
  (1 / ((n : ℝ) + 1)) * ∑ m ∈ Finset.Icc 1 (n + 1), ((-1 : ℝ) ^ (m - 1) / (m : ℝ)) *
    ∑ rs ∈ (Fintype.piFinset fun _ : Fin m =>
        Finset.range (n + 2) ×ˢ Finset.range (n + 2)).filter
        (fun rs => (∀ i, 0 < (rs i).1 + (rs i).2) ∧ ∑ i, ((rs i).1 + (rs i).2) = n + 1),
      ipb P Q F G (word rs) z /
        ∏ i, (((rs i).1.factorial : ℝ) * ((rs i).2.factorial : ℝ))

/-- The truncated modified Hamiltonian `H^(N)_η = Σ_{j ≤ N} η^j H_j`. -/
noncomputable def truncH {d : ℕ} (P Q : Set (E d)) (F G : E d → ℝ) (N : ℕ) (η : ℝ) :
    E d × E d → ℝ := fun z =>
  ∑ j ∈ Finset.range (N + 1), η ^ j * corr P Q F G j z

/-- One step of symplectic Euler (5). -/
noncomputable def step {d : ℕ} (P Q : Set (E d)) (F G : E d → ℝ) (η : ℝ) (z : E d × E d) :
    E d × E d :=
  let p' := z.1 - η • gradientWithin G Q z.2
  (p', z.2 + η • gradientWithin F P p')

theorem main : ∃ Φ : ℕ → ℚ, Monotone Φ ∧ (∃ C : ℚ, ∀ N, Φ N ≤ C) ∧
    ∀ (d : ℕ) (P Q : Set (E d)) (F G : E d → ℝ) (L : ℝ) (N : ℕ),
      IsClosed P → Convex ℝ P → (interior P).Nonempty →
      IsClosed Q → Convex ℝ Q → (interior Q).Nonempty →
      0 < L → LSmoothUpTo F P L (N + 2) → LSmoothUpTo G Q L (N + 2) →
      ∀ η : ℝ, 0 < η → ∀ (z : ℕ → E d × E d) (k : ℕ),
        (∀ j ≤ k, z j ∈ P ×ˢ Q) → (∀ j < k, z (j + 1) = step P Q F G η (z j)) →
        |truncH P Q F G N η (z k) - truncH P Q F G N η (z 0)|
          ≤ (k : ℝ) * (Φ N : ℝ) * L ^ (N + 3) * η ^ (N + 2) := by
  sorry

end OMA.S_arxiv_2405_03472
