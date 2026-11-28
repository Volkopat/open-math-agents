import OMAReductions.R_wpc_vp_vs_vnp_R1_H2_R1

/-! Leaf H1 of reductions/wpc-vp-vs-vnp.R1.H2.R1: scalar descent of exact circuits.
Circuit model, Nullstellensatz descent, scalar relabeling and the table/circuit
correspondence are adapted from OpenAI, math, lean/OAI/Computability/VPVNP
(CircuitSize, CircuitDescent, ScalarDescent and ComparatorChallenges/VPVNP),
commit 3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0, Copyright OpenAI,
https://www.apache.org/licenses/LICENSE-2.0 . Changes: concatenated, unused parts
removed, table model taken from the statement file. -/

section

/-! # Exact arithmetic circuits and projections

Gates are listed in topological order. Each operand may use any earlier gate, a variable,
or any scalar in the coefficient ring. Only binary operations count toward the size.
The designated output is evaluated in the ring of formal multivariate polynomials.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- A binary addition, subtraction, or multiplication gate in an exact arithmetic circuit. -/
inductive BinOp where
  | add | sub | mul

/-- Interpret a gate's operation on its two ordered inputs in the target ring. -/
def BinOp.apply {A : Type*} [Ring A] : BinOp → A → A → A
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- A reference available after exactly `n` gates have been computed. -/
inductive Ref (R σ : Type*) (n : ℕ) where
  | var : σ → Ref R σ n
  | const : R → Ref R σ n
  | gate : Fin n → Ref R σ n

/-- A topologically ordered list of arithmetic gates. The index counts the gates already
available to subsequent operands. -/
inductive Program (R σ : Type*) : ℕ → Type _ where
  | nil : Program R σ 0
  | snoc {n : ℕ} (prev : Program R σ n) (op : BinOp) (a b : Ref R σ n) : Program R σ (n+1)

/-- An arithmetic program with one designated output. Its size index counts binary operations. -/
structure Circuit (R σ : Type*) (n : ℕ) where
  /-- The sequence of binary gates available to the output reference. -/
  program : Program R σ n
  /-- The input variable, ring constant, or previously computed gate selected as the output. -/
  output : Ref R σ n

variable {R S σ τ A B : Type*} {n : ℕ}

/-- Resolve an operand using the supplied interpretation of constants, inputs, and earlier gate
values. -/
def Ref.read (scalar : R → A) (input : σ → A) (wires : Fin n → A) : Ref R σ n → A
  | .const r => scalar r
  | .var i => input i
  | .gate i => wires i

/-- Evaluate the gates in topological order and return the value at every gate index. -/
def Program.run [Ring A] (scalar : R → A) (input : σ → A) :
    {n : ℕ} → Program R σ n → Fin n → A
  | _, .nil => Fin.elim0
  | _, .snoc p op a b =>
    let wires := p.run scalar input
    Fin.lastCases (op.apply (a.read scalar input wires) (b.read scalar input wires)) wires

/-- Read the designated output after evaluating the circuit with the supplied scalar and
variable assignments. -/
def Circuit.eval [Ring A] (c : Circuit R σ n) (scalar : R → A) (input : σ → A) : A :=
  c.output.read scalar input (c.program.run scalar input)

/-- The formal polynomial computed when each input is its corresponding indeterminate and each
scalar is a constant polynomial. -/
noncomputable def Circuit.polynomial [CommRing R] (c : Circuit R σ n) : MvPolynomial σ R :=
  c.eval MvPolynomial.C MvPolynomial.X

/-- Substitutions allowed in a projection. A variable may become a variable or a scalar. -/
abbrev Projection (R σ τ : Type*) := σ → τ ⊕ R

/-- Apply a projection to a variable operand and the supplied scalar map to a constant operand.
A gate reference keeps its index. -/
def Ref.subst (φ : Projection S σ τ) (f : R → S) : Ref R σ n → Ref S τ n
  | .var i => (φ i).elim Ref.var Ref.const
  | .const r => .const (f r)
  | .gate i => .gate i

/-- Project the variable operands and map the constants of every gate in the program. -/
def Program.subst (φ : Projection S σ τ) (f : R → S) :
    {n : ℕ} → Program R σ n → Program S τ n
  | _, .nil => .nil
  | _, .snoc p op a b => .snoc (p.subst φ f) op (a.subst φ f) (b.subst φ f)

/-- Apply the same variable projection and scalar map to the program and its designated output
reference. -/
def Circuit.subst (c : Circuit R σ n) (φ : Projection S σ τ) (f : R → S) : Circuit S τ n :=
  ⟨c.program.subst φ f, c.output.subst φ f⟩

/-- Specialize each scalar operand along the given map while retaining the circuit's input
variables. -/
def Circuit.mapConstants (c : Circuit R σ n) (f : R → S) : Circuit S σ n :=
  c.subst Sum.inl f

private theorem Ref.read_subst (φ : Projection S σ τ) (f : R → S)
    (s : S → A) (x : τ → A) (w : Fin n → A) (r : Ref R σ n) :
    (r.subst φ f).read s x w = r.read (s ∘ f) (fun i => (φ i).elim x s) w := by
  cases r with
  | var i => cases h : φ i <;> simp [Ref.subst, Ref.read, h]
  | const | gate => rfl

private theorem Program.run_subst [Ring A] (φ : Projection S σ τ) (f : R → S)
    (s : S → A) (x : τ → A) (p : Program R σ n) :
    (p.subst φ f).run s x = p.run (s ∘ f) (fun i => (φ i).elim x s) := by
  induction p with
  | nil => rfl
  | snoc p op a b ih => simp only [Program.subst, Program.run, ih, Ref.read_subst]

theorem Circuit.eval_subst [Ring A] (c : Circuit R σ n) (φ : Projection S σ τ)
    (f : R → S) (s : S → A) (x : τ → A) :
    (c.subst φ f).eval s x = c.eval (s ∘ f) (fun i => (φ i).elim x s) := by
  simp only [Circuit.eval, Circuit.subst, Program.run_subst, Ref.read_subst]

private theorem Ref.read_hom [Ring A] [Ring B] (h : A →+* B) (s : R → A) (x : σ → A)
    (w : Fin n → A) (r : Ref R σ n) :
    h (r.read s x w) = r.read (h ∘ s) (h ∘ x) (h ∘ w) := by cases r <;> rfl

private theorem Program.run_hom [Ring A] [Ring B] (h : A →+* B) (s : R → A) (x : σ → A)
    (p : Program R σ n) : h ∘ p.run s x = p.run (h ∘ s) (h ∘ x) := by
  induction p with
  | nil => funext j; exact j.elim0
  | snoc p op a b ih =>
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Function.comp_apply, Program.run, Fin.lastCases_last]
      cases op <;> simp [BinOp.apply, Ref.read_hom, ih]
    · simpa [Program.run, Function.comp_def] using congrFun ih i

theorem Circuit.eval_hom [Ring A] [Ring B] (c : Circuit R σ n) (h : A →+* B)
    (s : R → A) (x : σ → A) : h (c.eval s x) = c.eval (h ∘ s) (h ∘ x) := by
  simp only [Circuit.eval, Ref.read_hom, Program.run_hom]

/-- Scalar specialization preserves every binary gate of the circuit. -/
theorem Circuit.map_polynomial [CommRing R] [CommRing S] (c : Circuit R σ n) (f : R →+* S) :
    (c.mapConstants f).polynomial = MvPolynomial.map f c.polynomial := by
  rw [Circuit.mapConstants, Circuit.polynomial, Circuit.eval_subst, Circuit.polynomial,
    Circuit.eval_hom]
  congr 1 <;> funext i <;> simp

/-- The coefficient-preserving polynomial semiring homomorphism substituting each source
variable by its prescribed target variable or scalar. -/
noncomputable def Projection.hom [CommSemiring R] (φ : Projection R σ τ) :
    MvPolynomial σ R →+* MvPolynomial τ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => (φ i).elim MvPolynomial.X MvPolynomial.C)

/-- Projecting a formal polynomial computed with `n` gates gives an `n`-gate circuit. -/
theorem Circuit.project_polynomial [CommRing R] (c : Circuit R σ n) (φ : Projection R σ τ) :
    (c.subst φ id).polynomial = φ.hom c.polynomial := by
  rw [Circuit.polynomial, Circuit.eval_subst, Circuit.polynomial, Circuit.eval_hom]
  congr 1 <;> funext i <;> simp [Projection.hom]

end VPVNP
end Computability
end OAI

end

section

/-!
# Descent of exact polynomial computations

Section 1 of *VP and VNP differ over every field* passes from a circuit over an
arbitrary field to the same circuit topology over the algebraic closure of the prime
field. Each scalar input of the topology can first be replaced by a parameter. The
coefficients of the resulting formal output are polynomials in these parameters.
Hilbert's Nullstellensatz descends the simultaneous coefficient equations to any
algebraically closed extension of the base field.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {k F K σ υ : Type*} [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] [IsAlgClosed K] [Finite σ]

/-- A polynomial system in finitely many unknowns that has a solution in an extension
field of `k` has a solution in every algebraically closed extension of `k`. -/
theorem polynomialSystem_descent (S : Set (MvPolynomial σ k)) (a : σ → F)
    (ha : ∀ p ∈ S, aeval a p = 0) :
    ∃ b : σ → K, ∀ p ∈ S, aeval b p = 0 := by
  have hproper : Ideal.span S ≠ ⊤ := by
    have hle : Ideal.span S ≤ vanishingIdeal k {a} :=
      Ideal.span_le.mpr fun p hp ↦ (mem_vanishingIdeal_singleton_iff a p).mpr (ha p hp)
    exact fun h ↦ (inferInstance : (vanishingIdeal k {a}).IsPrime).ne_top <|
      top_unique (h ▸ hle)
  obtain ⟨M, hM, hSM⟩ := Ideal.exists_le_maximal (Ideal.span S) hproper
  obtain ⟨b, rfl⟩ := eq_vanishingIdeal_singleton_of_isMaximal K hM
  exact ⟨b, fun p hp ↦ (mem_vanishingIdeal_singleton_iff b p).mp
    (hSM (Ideal.subset_span hp))⟩

/-- An exact specialization of a formal output polynomial over a parameter ring descends
simultaneously in all its coefficients. This applies to a circuit with any degree of
intermediate cancellation, using its scalar inputs as the parameters. -/
theorem formalOutput_descent (P : MvPolynomial υ (MvPolynomial σ k)) (f : MvPolynomial υ k)
    (a : σ → F) (ha : map (aeval a).toRingHom P = map (algebraMap k F) f) :
    ∃ b : σ → K, map (aeval b).toRingHom P = map (algebraMap k K) f := by
  let eqn (m : υ →₀ ℕ) : MvPolynomial σ k := P.coeff m - C (f.coeff m)
  obtain ⟨b, hb⟩ := polynomialSystem_descent (K := K) (Set.range eqn) a (by
    rintro _ ⟨m, rfl⟩
    have h := congrArg (fun p : MvPolynomial υ F ↦ p.coeff m) ha
    simpa [eqn, sub_eq_zero, coeff_map] using h)
  refine ⟨b, MvPolynomial.ext _ _ fun m ↦ ?_⟩
  have h := hb (eqn m) (Set.mem_range_self m)
  simpa [eqn, sub_eq_zero, coeff_map] using h

end VPVNP
end Computability
end OAI

end


section

/-!
# Descent without changing the circuit topology

A circuit for a polynomial defined over a base field `k` can replace every scalar
label with a new value in an algebraically closed extension of `k`. This applies
when the original labels belong to an arbitrary extension of `k`. Binary gate
types, wiring, reuse, the designated output and the gate count all persist.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {R S T σ : Type*} {n : ℕ}

private def Ref.scalarLabels : Ref R σ n → List R
  | .const c => [c]
  | .var _ | .gate _ => []

private def Program.scalarLabels : {n : ℕ} → Program R σ n → List R
  | _, .nil => []
  | _, .snoc p _ a b => p.scalarLabels ++ a.scalarLabels ++ b.scalarLabels

/-- All scalar occurrences in a circuit, including an output that is a scalar. -/
def Circuit.scalarLabels (c : Circuit R σ n) : List R :=
  c.program.scalarLabels ++ c.output.scalarLabels

private theorem Ref.subst_inl_comp (r : Ref R σ n) (f : R → S) (g : S → T) :
    (r.subst Sum.inl f).subst Sum.inl g = r.subst Sum.inl (g ∘ f) := by cases r <;> rfl

private theorem Program.subst_inl_comp (p : Program R σ n) (f : R → S) (g : S → T) :
    (p.subst Sum.inl f).subst Sum.inl g = p.subst Sum.inl (g ∘ f) := by
  induction p with
  | nil => rfl
  | snoc p op a b ih => simp only [Program.subst, ih, Ref.subst_inl_comp]

theorem Circuit.mapConstants_comp (c : Circuit R σ n) (f : R → S) (g : S → T) :
    (c.mapConstants f).mapConstants g = c.mapConstants (g ∘ f) := by
  simp only [Circuit.mapConstants, Circuit.subst, Ref.subst_inl_comp, Program.subst_inl_comp]

private theorem Ref.subst_inl_self (r : Ref R σ n) (f : R → R)
    (hf : ∀ x ∈ r.scalarLabels, f x = x) : r.subst Sum.inl f = r := by
  cases r with
  | const x => simp [Ref.subst, hf x (by simp [Ref.scalarLabels])]
  | var | gate => rfl

private theorem Program.subst_inl_self (p : Program R σ n) (f : R → R)
    (hf : ∀ x ∈ p.scalarLabels, f x = x) : p.subst Sum.inl f = p := by
  induction p with
  | nil => rfl
  | snoc p op a b ih =>
    rw [Program.subst, ih (fun x hx ↦ hf x (by simp [Program.scalarLabels, hx])),
      a.subst_inl_self f (fun x hx ↦ hf x (by simp [Program.scalarLabels, hx])),
      b.subst_inl_self f (fun x hx ↦ hf x (by simp [Program.scalarLabels, hx]))]

theorem Circuit.mapConstants_self (c : Circuit R σ n) (f : R → R)
    (hf : ∀ x ∈ c.scalarLabels, f x = x) : c.mapConstants f = c := by
  simp only [Circuit.mapConstants, Circuit.subst,
    c.program.subst_inl_self f (fun x hx ↦ hf x (by simp [Circuit.scalarLabels, hx])),
    c.output.subst_inl_self f (fun x hx ↦ hf x (by simp [Circuit.scalarLabels, hx]))]

/-- Descent of an exact circuit by changing only its scalar labels. The formal target
polynomial is interpreted in the two fields by their respective algebra maps. -/
theorem Circuit.exists_scalar_relabeling {k F K : Type*} [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] [IsAlgClosed K] (c : Circuit F σ n) (p : MvPolynomial σ k)
    (hc : c.polynomial = map (algebraMap k F) p) :
    ∃ relabel : F → K, (c.mapConstants relabel).polynomial = map (algebraMap k K) p := by
  classical
  let labels := c.scalarLabels.toFinset
  let param (v : F) : MvPolynomial (↥labels) k :=
    if h : v ∈ labels then X ⟨v, h⟩ else 0
  let generic := c.mapConstants param
  let values : (↥labels) → F := Subtype.val
  have recover : generic.mapConstants (aeval values).toRingHom = c := by
    rw [Circuit.mapConstants_comp]
    apply Circuit.mapConstants_self
    intro v hv
    have hv' : v ∈ labels := List.mem_toFinset.mpr hv
    simp [param, values, hv']
  have hs : map (aeval values).toRingHom generic.polynomial = map (algebraMap k F) p := by
    rw [← Circuit.map_polynomial, recover, hc]
  obtain ⟨b, hb⟩ := formalOutput_descent (K := K) generic.polynomial p values hs
  exact ⟨(aeval b).toRingHom ∘ param, by
    rw [← Circuit.mapConstants_comp, Circuit.map_polynomial]
    exact hb⟩

end VPVNP
end Computability
end OAI

end

section

/-! # Exact circuit correspondence for the project permanent-completeness statement -/

namespace OAI
namespace Computability
namespace VPVNP

namespace Valiant.Project

open OMA.S_wpc_vp_vs_vnp (Computes)

open MvPolynomial (C X)

variable {F σ : Type*} [Field F] {s k : ℕ}

private abbrev available (v : Fin s → MvPolynomial σ F) (k : ℕ) (x : MvPolynomial σ F) : Prop :=
  (∃ j : σ, X j = x) ∨ (∃ a : F, C a = x) ∨ ∃ j : Fin s, j.val < k ∧ v j = x

private abbrev prefixValues (v : Fin s → MvPolynomial σ F) (hk : k ≤ s) (i : Fin k) :=
  v (i.castLE hk)

private abbrev gateValue (allowed : MvPolynomial σ F → Prop) (x : MvPolynomial σ F) : Prop :=
  ∃ a b, allowed a ∧ allowed b ∧ (x = a + b ∨ x = a - b ∨ x = a * b)

private theorem available_iff_ref (v : Fin s → MvPolynomial σ F) (hk : k ≤ s)
    (x : MvPolynomial σ F) :
    available v k x ↔ ∃ r : Ref F σ k, r.read C X (prefixValues v hk) = x := by
  constructor
  · rintro (⟨j, rfl⟩ | ⟨c, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨.var j, rfl⟩
    · exact ⟨.const c, rfl⟩
    · exact ⟨.gate ⟨j, hj⟩, rfl⟩
  · rintro ⟨r, rfl⟩
    cases r with
    | var j => exact Or.inl ⟨j, rfl⟩
    | const c => exact Or.inr (Or.inl ⟨c, rfl⟩)
    | gate j => exact Or.inr (Or.inr ⟨j.castLE hk, j.isLt, rfl⟩)

private theorem gateValue_iff (v : Fin s → MvPolynomial σ F) (hk : k ≤ s)
    (x : MvPolynomial σ F) :
    gateValue (available v k) x ↔ ∃ op : BinOp, ∃ a b : Ref F σ k,
      op.apply (a.read C X (prefixValues v hk)) (b.read C X (prefixValues v hk)) = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hx⟩
    obtain ⟨ra, rfl⟩ := (available_iff_ref v hk a).mp ha
    obtain ⟨rb, rfl⟩ := (available_iff_ref v hk b).mp hb
    rcases hx with rfl | rfl | rfl
    · exact ⟨.add, ra, rb, rfl⟩
    · exact ⟨.sub, ra, rb, rfl⟩
    · exact ⟨.mul, ra, rb, rfl⟩
  · rintro ⟨op, a, b, rfl⟩
    refine ⟨_, _, (available_iff_ref v hk _).mpr ⟨a, rfl⟩,
      (available_iff_ref v hk _).mpr ⟨b, rfl⟩, ?_⟩
    cases op with
    | add => exact Or.inl rfl
    | sub => exact Or.inr (Or.inl rfl)
    | mul => exact Or.inr (Or.inr rfl)

private theorem run_snoc_last (q : Program F σ s) (op : BinOp) (a b : Ref F σ s) :
    (q.snoc op a b).run C X (Fin.last s) =
      op.apply (a.read C X (q.run C X)) (b.read C X (q.run C X)) := by
  simp only [Program.run, Fin.lastCases_last]

private theorem run_snoc_castSucc (q : Program F σ s) (op : BinOp) (a b : Ref F σ s)
    (i : Fin s) : (q.snoc op a b).run C X i.castSucc = q.run C X i := by
  simp only [Program.run, Fin.lastCases_castSucc]

/-- Build a program for a prefix without duplicating any of its referenced gates. -/
private theorem realize_prefix (v : Fin s → MvPolynomial σ F)
    (h : ∀ i : Fin s, gateValue (available v i.val) (v i)) (k : ℕ) (hk : k ≤ s) :
    ∃ q : Program F σ k, q.run C X = prefixValues v hk := by
  induction k with
  | zero => exact ⟨.nil, Subsingleton.elim _ _⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih (Nat.le_of_succ_le hk)
    let i : Fin s := ⟨k, hk⟩
    obtain ⟨op, a, b, hop⟩ := (gateValue_iff v (Nat.le_of_succ_le hk) (v i)).mp (h i)
    refine ⟨q.snoc op a b, ?_⟩
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [run_snoc_last, hq]
      exact hop
    · rw [run_snoc_castSucc]
      exact congrFun hq j

/-- Reading a program as a table recovers legal operands at every position. -/
private theorem program_gate (q : Program F σ s) (i : Fin s) :
    gateValue (available (q.run C X) i.val) (q.run C X i) := by
  induction q with
  | nil => exact i.elim0
  | @snoc s q op a b ih =>
    let v := q.run C X
    let v' := (q.snoc op a b).run C X
    have previous (k : ℕ) (hk : k ≤ s) :
        prefixValues v' (Nat.le_succ_of_le hk) = prefixValues v hk := by
      funext j
      exact run_snoc_castSucc q op a b (j.castLE hk)
    cases i using Fin.lastCases with
    | last =>
      apply (gateValue_iff v' (Nat.le_succ s) _).mpr
      refine ⟨op, a, b, ?_⟩
      rw [previous s le_rfl]
      exact (run_snoc_last q op a b).symm
    | cast j =>
      obtain ⟨op', a', b', hj⟩ := (gateValue_iff v j.isLt.le _).mp (ih j)
      apply (gateValue_iff v' (Nat.le_succ_of_le j.isLt.le) _).mpr
      refine ⟨op', a', b', ?_⟩
      rw [previous j.val j.isLt.le]
      exact hj.trans (run_snoc_castSucc q op a b j).symm

/-- The self-contained table model and the project's exact circuits compute precisely
the same formal polynomials with exactly the same number of binary gates. -/
theorem computes_iff {s : ℕ} {p : MvPolynomial σ F} :
    Computes s p ↔ ∃ c : VPVNP.Circuit F σ s, c.polynomial = p := by
  constructor
  · rintro ⟨v, hout, h⟩
    obtain ⟨q, hq⟩ := realize_prefix v h s le_rfl
    obtain ⟨r, hr⟩ := (available_iff_ref v le_rfl p).mp hout
    refine ⟨⟨q, r⟩, ?_⟩
    change r.read C X (q.run C X) = p
    rwa [hq]
  · rintro ⟨c, rfl⟩
    exact ⟨c.program.run C X, (available_iff_ref _ le_rfl _).mpr ⟨c.output, rfl⟩,
      program_gate c.program⟩

end Valiant.Project

end VPVNP
end Computability
end OAI

end

namespace OMA.P_wpc_vp_vs_vnp_R1_H2_R1_H1

open MvPolynomial OAI.Computability.VPVNP
open scoped Classical

/-- The directed Hamiltonian-cycle polynomial exactly as written in the step. -/
noncomputable def hcp (R : Type*) [CommSemiring R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => 0 < n ∧ π.IsCycleOn Set.univ),
    ∏ i, (X (i, π i) : MvPolynomial (Fin n × Fin n) R)

theorem map_hcp {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (n : ℕ) :
    map f (hcp R n) = hcp S n := by
  simp only [hcp, map_sum, map_prod, map_X]

/-- An exact `s`-gate table over `F` is relabeled to one over `K`, gate for gate. -/
theorem transfer {k F K : Type*} [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    [IsAlgClosed K] (n s : ℕ) (h : OMA.S_wpc_vp_vs_vnp.Computes s (hcp F n)) :
    OMA.S_wpc_vp_vs_vnp.Computes s (hcp K n) := by
  obtain ⟨c, hc⟩ := Valiant.Project.computes_iff.mp h
  obtain ⟨f, hf⟩ := c.exists_scalar_relabeling (k := k) (K := K) (hcp k n)
    (by rw [hc, map_hcp])
  exact Valiant.Project.computes_iff.mpr ⟨_, hf.trans (map_hcp _ n)⟩

theorem countable_closure (k : Type) [Field k] [Countable k] : Countable (AlgebraicClosure k) :=
  Cardinal.mk_le_aleph0_iff.mp ((Algebra.IsAlgebraic.cardinalMk_le_max k (AlgebraicClosure k)).trans
    (max_le Cardinal.mk_le_aleph0 le_rfl))

end OMA.P_wpc_vp_vs_vnp_R1_H2_R1_H1

open OMA.P_wpc_vp_vs_vnp_R1_H2_R1_H1 in
theorem OMA.solution : OMA.R_wpc_vp_vs_vnp_R1_H2_R1.H1 := by
  intro F _
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hq | h0
  · have : Fact (ringChar F).Prime := ⟨hq⟩
    let : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
    exact ⟨AlgebraicClosure (ZMod (ringChar F)), inferInstance, inferInstance,
      countable_closure _, fun n s h => transfer (k := ZMod (ringChar F)) n s h⟩
  · have : CharP F 0 := h0 ▸ ringChar.charP F
    have : CharZero F := CharP.charP_to_charZero F
    let : Algebra ℚ F := (Rat.castHom F).toAlgebra
    exact ⟨AlgebraicClosure ℚ, inferInstance, inferInstance,
      countable_closure _, fun n s h => transfer (k := ℚ) n s h⟩
