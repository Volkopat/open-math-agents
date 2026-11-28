import Mathlib

/-!
# The Sperner question for ordered set partitions

Giovanni Rossi asks whether an antichain of ordered partitions of an n-element set
can exceed its largest level. An ordered partition into k blocks is encoded by a
surjection to the ordered set Fin k. Combining consecutive blocks corresponds to
postcomposing with an order-preserving surjection. The level size is k! S(n,k).

Source: https://mathoverflow.net/questions/515645
Further work: G. Rossi, https://arxiv.org/abs/2611.34537
Credit: @Aryan-Poonacha
-/

namespace OMA.S_mo_515645

/-- A surjection onto k ordered labels specifies the nonempty blocks in order. -/
abbrev OrderedPartition (n : ℕ) :=
  Σ k : Fin (n + 1), {f : Fin n → Fin k.val // Function.Surjective f}

/-- The coarser partition is obtained by merging consecutive blocks. -/
def Refines {n : ℕ} (x y : OrderedPartition n) : Prop :=
  ∃ g : Fin x.1.val → Fin y.1.val, Monotone g ∧ Function.Surjective g ∧
    ∀ i, g (x.2.val i) = y.2.val i

/-- Every antichain is no larger than some level of the ordered partition poset. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ A : Finset (OrderedPartition n),
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ Refines x y) →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ A.card ≤ k.factorial * Nat.stirlingSecond n k := by
  sorry

end OMA.S_mo_515645
