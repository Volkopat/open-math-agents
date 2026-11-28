import Mathlib

/-!
# Maximizing total variation utility under a total variation privacy constraint

Source: math-Student, https://mathoverflow.net/questions/154572 (CC BY-SA 3.0).
Credit: @connoranderson.

The joint law P of X and V is given. A stochastic matrix K generates Z from X,
so V-X-Z is Markov. For prescribed finite Z the answer is the largest optimum
among finitely many linear objectives. When the output alphabet may be chosen,
one linear program suffices, with output labels the subsets of X and a fixed
objective. Both optima are attained. The slack variables linearize the privacy
constraint. Related work on linear programs for total variation privacy is
Rassouli and Gündüz, https://arxiv.org/abs/1801.02505.
-/

namespace OMA.S_mo_154572

variable {X V Z : Type} [Fintype X] [Fintype V] [Fintype Z]

def Joint (P : X → V → ℝ) : Prop := (∀ x v, 0≤P x v) ∧ (∑ x, ∑ v, P x v)=1
def Channel (K : X → Z → ℝ) : Prop := (∀ x z, 0≤K x z) ∧ ∀ x, ∑ z, K x z=1
def px (P : X → V → ℝ) (x : X) := ∑ v, P x v
def pv (P : X → V → ℝ) (v : V) := ∑ x, P x v
def pz (P : X → V → ℝ) (K : X → Z → ℝ) (z : Z) := ∑ x, px P x*K x z
def dx (P : X → V → ℝ) (K : X → Z → ℝ) (x : X) (z : Z) := px P x*(K x z-pz P K z)
def dv (P : X → V → ℝ) (K : X → Z → ℝ) (v : V) (z : Z) :=
  (∑ x, P x v*K x z) - pv P v*pz P K z

noncomputable def utility (P : X → V → ℝ) (K : X → Z → ℝ) := (∑ z, ∑ x, |dx P K x z|)/2
noncomputable def leakage (P : X → V → ℝ) (K : X → Z → ℝ) := (∑ z, ∑ v, |dv P K v z|)/2

noncomputable def score [DecidableEq X] (P : X → V → ℝ) (K : X → Z → ℝ) (s : Z → Finset X) :=
  (∑ z, ∑ x, (if x ∈ s z then 1 else -1)*dx P K x z)/2

def FeasibleLP (P : X → V → ℝ) (ε : ℝ) (K : X → Z → ℝ) (h : V → Z → ℝ) : Prop :=
  Channel K ∧ (∀ v z, dv P K v z ≤ h v z ∧ -dv P K v z ≤ h v z) ∧
    (∑ z, ∑ v, h v z) ≤ 2*ε

def values (P : X → V → ℝ) (ε : ℝ) (Z : Type) [Fintype Z] : Set ℝ :=
  {t | ∃ K : X → Z → ℝ, Channel K ∧ leakage P K ≤ ε ∧ utility P K=t}

def lpValues [DecidableEq X] (P : X → V → ℝ) (ε : ℝ) (s : Z → Finset X) : Set ℝ :=
  {t | ∃ (K : X → Z → ℝ) (h : V → Z → ℝ), FeasibleLP P ε K h ∧ score P K s=t}

def allValues (P : X → V → ℝ) (ε : ℝ) : Set ℝ :=
  {t | ∃ (Z : Type) (fZ : Fintype Z), t ∈ @values X V _ _ P ε Z fZ}

theorem main : ∀ {X V : Type} [Fintype X] [Fintype V] [DecidableEq X] (P : X → V → ℝ),
    Joint P → ∀ ε : ℝ, 0<ε →
    (∀ (Z : Type) [Fintype Z] [Nonempty Z], ∃ m : ℝ,
      IsGreatest (values P ε Z) m ∧ IsGreatest (⋃ s : Z → Finset X, lpValues P ε s) m) ∧
    (∃ m : ℝ, IsGreatest (allValues P ε) m ∧ IsGreatest (lpValues P ε (id : Finset X → Finset X)) m) := by
  sorry

end OMA.S_mo_154572
