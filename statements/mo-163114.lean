import Mathlib

/-!
# Does a BCL algebra define a partial order?

Source: https://mathoverflow.net/questions/163114
Credit: @koolkao

Question (Ioachim Drugus, MathOverflow 163114, 2014; CC BY-SA 3.0). A BCL algebra is a universal
algebra with a binary operation denoted as `*` and a `0`-ary operation (constant) denoted as `0`,
satisfying the following axioms:
(1) `x * x = 0`;
(2) if `x * y = 0` and `y * x = 0`, then `x = y`;
(3) `(((x * y) * z) * ((x * z) * y)) * ((z * y) * x) = 0`.
This definition is from the article "A New Branch of the Pure Algebra: BCL-Algebras" by Yonghong
Liu published in Advances in Pure Mathematics, 2011, 1, 297-299. The author also defines a
relationship `x ⩽ y` iff `x * y = 0`. Without any proof, this relationship is said to be partial
order. While it is obviously reflexive and antisymmetric, I find it impossible to prove that it
is also transitive. Can anybody help?

`main` states the claim of the cited article: in every BCL algebra the relation `x ⩽ y ↔ x * y = 0`
is a partial order (reflexive, antisymmetric and transitive). A disproof is a counterexample.

Translation choices:
* a BCL algebra is a type `A` with a binary operation `op : A → A → A` (written `*` in the source)
  and a constant `z : A` (written `0`), satisfying axioms (1)–(3) for all elements; `A` lives in
  `Type`, and the claim is invariant under isomorphism;
* the relation is `x ⩽ y ↔ op x y = z`, and "partial order" means reflexive, antisymmetric and
  transitive (all three are stated, although reflexivity and antisymmetry are axioms (1) and (2)).
-/

namespace OMA.S_mo_163114

/-- The axioms (1)–(3) of a BCL algebra `(A, op, z)`. -/
def IsBCL {A : Type} (op : A → A → A) (z : A) : Prop :=
  (∀ x, op x x = z) ∧
  (∀ x y, op x y = z → op y x = z → x = y) ∧
  (∀ x y w, op (op (op (op x y) w) (op (op x w) y)) (op (op w y) x) = z)

/-- In every BCL algebra, `x ⩽ y ↔ x * y = 0` is a partial order. -/
theorem main :
    ∀ (A : Type) (op : A → A → A) (z : A), IsBCL op z →
      (∀ x, op x x = z) ∧ (∀ x y, op x y = z → op y x = z → x = y) ∧
        (∀ x y w, op x y = z → op y w = z → op x w = z) := by
  sorry

end OMA.S_mo_163114
