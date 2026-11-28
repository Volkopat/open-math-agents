import Mathlib

/-!
# On the Factor Complexity Associated with a Family of Multidimensional Continued Fraction Algorithms

Source: Thomas Garrity and Otto Vaughn Osterman, arXiv:2410.02032.
Journal: Combinatorics and Number Theory 15 (2026), Conjecture 53.
In the arXiv preprint the same claim is Conjecture 1, and the language and
complexity definitions are Definition 12 and Definition 5. The journal text
numbers the language definition as Definition 14.
Credit: @mjkang-estrella

The claim formalized here is the remaining case named in the abstract: for the
TRIP map S(e,23,e), every S(e,23,e)-adic language L satisfies p_L(n) ≤ 3n.
Section 10 of the preprint gives the two substitutions on the alphabet {1,2,3}:

  S0(e,23,e):  1 ↦ 2,  2 ↦ 13,  3 ↦ 3
  S1(e,23,e):  1 ↦ 1,  2 ↦ 2,   3 ↦ 13

An S(e,23,e)-adic language is the language of a coding sequence drawn from
this pair. Definition 12 says that the language of σ = (σ₀, σ₁, σ₂, …) is the
set of factors of (σ₀ ∘ σ₁ ∘ ⋯ ∘ σ_{n-1})(c) for some n ∈ ℕ and some letter c.
The preprint writes ℕ⁰ when zero is included (Definition 3) and ℕ in Definition
12, so the composition is required to have positive length. No primitivity,
recurrence, or rational-independence hypothesis is imposed: the quantifier is
every coding sequence.

Encoding. Letters 1, 2, 3 are `0, 1, 2 : Fin 3`. A directive `d : ℕ → Bool`
uses `false` for S0 and `true` for S1. `prefImage d r` is the length-r prefix
composition with `d 0` outermost, so `prefImage d r` is σ₀ ∘ ⋯ ∘ σ_{r-1}.
A factor is a contiguous subword (`List.IsInfix`, written `<:+:`), as in
Definition 3. Complexity is `Nat.card` of the length-n words in the language,
which is the number of distinct words of length n in Definition 5; the
development proves each length slice is finite.

The audited endpoint `Trip.lang` also admits the empty composition (depth 0).
For these two substitutions every letter occurs in an S0-image and in an
S1-image, so the depth-0 and positive-depth descriptions define the same set
of words (`lang_iff_pos_level` in the proof). `main` follows the paper and
requires positive length.

The journal wording of Conjecture 53 adds five conjugates and six twins of
S(e,23,e). The preprint statement (Conjecture 1) does not. Conjugacy and
twinning preserve complexity by the preprint's Propositions 21 and 22 (the
remarks immediately above them record that a letter permutation and reversal
preserve complexity; the formalization notes call the corresponding journal
results Propositions 45 and 47). Those reductions are not formalized here.
The theorem is the bound for S(e,23,e)-adic languages.
-/

namespace OMA.S_arxiv_2410_02032

abbrev Letter := Fin 3

abbrev Word := List Letter

/-- S0(e,23,e): 1 ↦ 2, 2 ↦ 13, 3 ↦ 3. -/
def S0 (c : Letter) : Word :=
  if c = 0 then [1] else if c = 1 then [0, 2] else [2]

/-- S1(e,23,e): 1 ↦ 1, 2 ↦ 2, 3 ↦ 13. -/
def S1 (c : Letter) : Word :=
  if c = 0 then [0] else if c = 1 then [1] else [0, 2]

/-- Apply one substitution: `false` is S0 and `true` is S1. -/
def subst (b : Bool) (w : Word) : Word :=
  w.flatMap (if b then S1 else S0)

/-- Length-r prefix composition. `d 0` is outermost. Depth 0 is the identity. -/
def prefImage (d : ℕ → Bool) : ℕ → Word → Word
  | 0, w => w
  | r + 1, w => prefImage d r (subst (d r) w)

/-- Language of the coding sequence `d`, Definition 12: factors of a positive-length
prefix composition applied to a single letter. -/
def lang (d : ℕ → Bool) (w : Word) : Prop :=
  ∃ (r : ℕ) (c : Letter), 1 ≤ r ∧ w <:+: prefImage d r [c]

/-- Factor complexity, Definition 5. -/
noncomputable def complexity (L : Word → Prop) (n : ℕ) : ℕ :=
  Nat.card {w : Word // w.length = n ∧ L w}

/-- Conjecture 53 / arXiv Conjecture 1: p_L(n) ≤ 3n for every S(e,23,e)-adic language. -/
theorem main :
    ∀ (d : ℕ → Bool) (n : ℕ), 1 ≤ n → complexity (lang d) n ≤ 3 * n := by
  sorry

end OMA.S_arxiv_2410_02032
