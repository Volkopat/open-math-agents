import FormalConjectures.Other.HyperbolicGroupsResiduallyFinite
import Mathlib

/-!
# A finite affine-space construction

Start with a nonidentity element killed by every finite image of a hyperbolic group A.
Take copies of A at the points of a finite affine three-space. For each point and
each nonidentity generator, impose a relator starting with that generator, followed
by 31 copies of the chosen element at other points on a line. The direction of the
line records both the generator and the first coordinate of the starting point.
Two points therefore determine the entire relator. In a finite image these
relations kill every generator of every factor.

H1 is the non-residual-finiteness theorem formalized by senamakel in PR 3425
from the OpenAI construction. H2 isolates
classical free-product small cancellation. In the free product modulo the displayed
relators, the factors embed and the quotient is hyperbolic relative to them
(Martin and Steenbock, Ann. Inst. Fourier 67 (2017), Section 2.1, Theorems 2.1 and 2.2).
Relative hyperbolicity with hyperbolic factors implies hyperbolicity. For H2,
distinct relators have at most one factor in common, and each factor occurs only
once per relator. Even allowing partial syllables at the ends, pieces have length
at most three, strictly less than one sixth of 32.
-/

namespace OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R2

def H1 : Prop := ¬ ∀ (A : Type) [Group A] [Group.IsHyperbolic A], Group.ResiduallyFinite A

/-- A finite family of sparse relators can be imposed on copies of a hyperbolic
group while keeping the factors embedded and the resulting group hyperbolic. -/
def H2 : Prop := ∀ (A : Type) [Group A] [Group.IsHyperbolic A]
    (V R : Type) [Finite V] [Finite R] (tag : R → Fin 32 → V) (letter : R → Fin 32 → A),
    (∀ r, Function.Injective (tag r)) →
    (∀ r s j k u v, j ≠ k → tag r j = tag s u → tag r k = tag s v → r = s) →
    (∀ r j, letter r j ≠ 1) →
    ∃ (Q : Type) (_ : Group Q) (_ : Group.IsHyperbolic Q) (e : V → A →* Q),
      (∀ v, Function.Injective (e v)) ∧ (⨆ v, (e v).range) = ⊤ ∧
      ∀ r, (List.ofFn fun j => e (tag r j) (letter r j)).prod = 1

/-- Two common points determine the slope parameters and the distinguished starting point. -/
lemma line_rigidity {K : Type} [Field K] (x y : K × K × K) (i l t u v w : K)
    (hne : t ≠ u)
    (h₁ : (x.1 + t, x.2.1 + x.1 * t, x.2.2 + i * t) = (y.1 + v, y.2.1 + y.1 * v, y.2.2 + l * v))
    (h₂ : (x.1 + u, x.2.1 + x.1 * u, x.2.2 + i * u) = (y.1 + w, y.2.1 + y.1 * w, y.2.2 + l * w)) :
    x = y ∧ i = l := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  obtain ⟨h₁a, h₁b, h₁c⟩ := Prod.mk.inj h₁ |>.imp_right Prod.mk.inj
  obtain ⟨h₂a, h₂b, h₂c⟩ := Prod.mk.inj h₂ |>.imp_right Prod.mk.inj
  dsimp at *
  have had : (a - d) * (t - u) = 0 := by linear_combination h₁b - h₂b - d * (h₁a - h₂a)
  have hil : (i - l) * (t - u) = 0 := by linear_combination h₁c - h₂c - l * (h₁a - h₂a)
  obtain rfl : a = d := sub_eq_zero.mp ((mul_eq_zero.mp had).resolve_right (sub_ne_zero.mpr hne))
  obtain rfl : i = l := sub_eq_zero.mp ((mul_eq_zero.mp hil).resolve_right (sub_ne_zero.mpr hne))
  obtain rfl : t = v := add_left_cancel h₁a
  exact ⟨by rw [add_right_cancel h₁b, add_right_cancel h₁c], rfl⟩

lemma cast_injective {p n : ℕ} (hn : n ≤ p) :
    Function.Injective (fun j : Fin n => (j.val : ZMod p)) := by
  intro j k h
  apply Fin.ext
  simpa only [ZMod.val_natCast_of_lt (j.isLt.trans_le hn),
    ZMod.val_natCast_of_lt (k.isLt.trans_le hn)] using congrArg ZMod.val h

theorem main : H1 → H2 → type_of% @HyperbolicGroupsResiduallyFinite.hyperbolic_exists_finiteIndex_ne_top := by
  classical
  intro hNonRF hSparse hProper
  apply hNonRF
  intro A _ _
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro a ha
  by_contra hUndetected
  have killed (F : Type) [Group F] [Finite F] (f : A →* F) : f a = 1 := by
    by_contra h
    exact hUndetected ⟨F, inferInstance, inferInstance, f, h⟩
  obtain ⟨n, P, _, _⟩ := Group.IsHyperbolic.exists_isHyperbolicWith A
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max n 32)
  have : Fact p.Prime := ⟨hprime⟩
  have hn : n ≤ p := (le_max_left ..).trans hp
  have h32 : 32 ≤ p := (le_max_right ..).trans hp
  -- The relator through x for generator i has direction (1, x.1, i).
  let V := ZMod p × ZMod p × ZMod p
  let R := V × {i : Fin n // P.val i ≠ 1}
  let tag (r : R) (j : Fin 32) : V :=
    let x := r.1
    let t : ZMod p := j.val
    (x.1 + t, x.2.1 + x.1 * t, x.2.2 + (r.2.val.val : ZMod p) * t)
  let letter (r : R) : Fin 32 → A := Fin.cases (P.val r.2.val) (fun _ => a)
  have injTag (r : R) : Function.Injective (tag r) := by
    intro j k h
    exact cast_injective h32 (add_left_cancel (congrArg Prod.fst h))
  have meet (r s : R) (j k u v : Fin 32) (hne : j ≠ k)
      (h₁ : tag r j = tag s u) (h₂ : tag r k = tag s v) : r = s := by
    obtain ⟨hx, hi⟩ := line_rigidity r.1 s.1 (r.2.val.val : ZMod p) (s.2.val.val : ZMod p)
      j.val k.val u.val v.val (fun h => hne (cast_injective h32 h)) h₁ h₂
    exact Prod.ext hx (Subtype.ext (cast_injective hn hi))
  have nonunit (r : R) (j : Fin 32) : letter r j ≠ 1 := by
    cases j using Fin.cases with
    | zero => exact r.2.property
    | succ k => exact ha
  obtain ⟨Q, _, _, e, he, hGen, hRel⟩ := hSparse A V R tag letter injTag meet nonunit
  let origin : V := (0, 0, 0)
  have : Nontrivial Q := ⟨⟨e origin a, e origin 1, (he origin).ne ha⟩⟩
  obtain ⟨H, hProperH, hFinite⟩ := hProper Q
  have : H.FiniteIndex := hFinite
  let f := MulAction.toPermHom Q (Q ⧸ H)
  -- The last 31 letters vanish in the finite permutation action on cosets.
  have factor (x : V) : f.comp (e x) = 1 := by
    apply P.hom_ext
    intro i
    by_cases hi : P.val i = 1
    · simp [hi]
    let r : R := (x, ⟨i, hi⟩)
    have h := congrArg f (hRel r)
    rw [map_one, List.ofFn_succ, List.prod_cons, map_mul, map_list_prod] at h
    have hTail : (List.map f (List.ofFn fun j : Fin 31 =>
        e (tag r j.succ) (letter r j.succ))).prod = 1 := by
      apply List.prod_eq_one
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
      exact killed _ (f.comp (e (tag r j.succ)))
    rw [hTail, mul_one] at h
    simpa [tag, letter, r] using h
  have hAll : (⊤ : Subgroup Q) ≤ f.ker := by
    rw [← hGen]
    refine iSup_le fun x q hq => ?_
    obtain ⟨b, rfl⟩ := hq
    exact MonoidHom.mem_ker.mpr (DFunLike.congr_fun (factor x) b)
  apply hProperH
  apply top_unique
  intro q hq
  apply H.normalCore_le
  rw [Subgroup.normalCore_eq_ker]
  exact hAll hq

end OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R2
