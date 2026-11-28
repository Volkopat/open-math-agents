import OMAReductions.R_Green14_W_3_13_R3

/-!
# Reflection of two disjoint blue gaps

Reflect the board about its midpoint and swap the two gaps whenever the
right gap has enough blue points and its reflected endpoints meet the
left-gap bounds. Among reversible configurations retain the orientation
whose four endpoints sum to at most 318. The red endpoints also exclude
all four possible red triples before any search over the rest of the board.

Credit: @wtho704. This is a reduction of @MrSeizy's two-gap formulation.
-/

namespace OMA.R_Green14_W_3_13_R3_H2_R1

private lemma endpoint_exclusions {R : ℕ → Prop} {p q u v : ℕ}
    (hpq : p < q) (hqu : q < u) (huv : u < v) (hv : v < 160)
    (left : R p ∧ R q ∧ ∀ x, p < x → x < q → ¬ R x)
    (right : R u ∧ R v ∧ ∀ x, u < x → x < v → ¬ R x)
    (free : ∀ a d, 0 < d → a + 2 * d < 160 → R a → R (a + d) → R (a + 2 * d) → False) :
    p + u ≠ 2 * q ∧ p + v ≠ 2 * q ∧ p + v ≠ 2 * u ∧ q + v ≠ 2 * u := by
  have excludes {a b c : ℕ} (hab : a < b) (hc : c < 160)
      (ra : R a) (rb : R b) (rc : R c) (equal : a + c = 2 * b) : False := by
    have middle : a + (b - a) = b := by omega
    have last : a + 2 * (b - a) = c := by omega
    exact free a (b - a) (by omega) (last.symm ▸ hc) ra (middle.symm ▸ rb) (last.symm ▸ rc)
  exact ⟨excludes hpq (by omega) left.1 left.2.1 right.1,
    excludes hpq hv left.1 left.2.1 right.2.1,
    excludes (by omega) hv left.1 right.1 right.2.1,
    excludes hqu hv left.2.1 right.1 right.2.1⟩

private lemma reflect_gap {R : ℕ → Prop} {a b : ℕ} (hab : a < b) (hb : b < 160)
    (gap : R a ∧ R b ∧ ∀ x, a < x → x < b → ¬ R x) :
    R (159 - (159 - b)) ∧ R (159 - (159 - a)) ∧
      ∀ x, 159 - b < x → x < 159 - a → ¬ R (159 - x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show 159 - (159 - b) = b by omega]
    exact gap.2.1
  · rw [show 159 - (159 - a) = a by omega]
    exact gap.1
  · intro x hx hy
    exact gap.2.2 (159 - x) (by omega) (by omega)

private lemma reflect_free {R : ℕ → Prop}
    (free : ∀ a d, 0 < d → a + 2 * d < 160 → R a → R (a + d) → R (a + 2 * d) → False) :
    ∀ a d, 0 < d → a + 2 * d < 160 →
      R (159 - a) → R (159 - (a + d)) → R (159 - (a + 2 * d)) → False := by
  intro a d hd ha first middle last
  apply free (159 - (a + 2 * d)) d hd (by omega) last
  · rw [show 159 - (a + 2 * d) + d = 159 - (a + d) by omega]
    exact middle
  · rw [show 159 - (a + 2 * d) + 2 * d = 159 - a by omega]
    exact first

private lemma reflect_meets {R : ℕ → Prop}
    (meets : ∀ a d, 0 < d → a + 12 * d < 160 → ∃ i : Fin 13, R (a + i.val * d)) :
    ∀ a d, 0 < d → a + 12 * d < 160 → ∃ i : Fin 13, R (159 - (a + i.val * d)) := by
  intro a d hd ha
  obtain ⟨i, hi⟩ := meets (159 - (a + 12 * d)) d hd (by omega)
  have bound : i.val ≤ 12 := by have := i.isLt; omega
  refine ⟨⟨12 - i.val, by omega⟩, ?_⟩
  have split : (12 - i.val) * d + i.val * d = 12 * d := by
    rw [← Nat.add_mul, Nat.sub_add_cancel bound]
  change R (159 - (a + (12 - i.val) * d))
  rw [show 159 - (a + (12 - i.val) * d) = 159 - (a + 12 * d) + i.val * d by omega]
  exact hi

private lemma reflect_five {R : ℕ → Prop}
    (five : ∀ o h : ℕ, 0 < h → o + 68 * h < 160 →
      ∃ a, a + 4 < 69 ∧ ∀ i : Fin 5, ¬ R (o + (a + i.val) * h)) :
    ∀ o h : ℕ, 0 < h → o + 68 * h < 160 →
      ∃ a, a + 4 < 69 ∧ ∀ i : Fin 5, ¬ R (159 - (o + (a + i.val) * h)) := by
  intro o h hh ho
  obtain ⟨a, ha, blue⟩ := five (159 - (o + 68 * h)) h hh (by omega)
  refine ⟨64 - a, by omega, ?_⟩
  intro i
  have bound := i.isLt
  let j : Fin 5 := ⟨4 - i.val, by omega⟩
  have split : (64 - a + i.val) + (a + (4 - i.val)) = 68 := by omega
  have products := congrArg (fun x : ℕ ↦ x * h) split
  rw [Nat.add_mul] at products
  have eqn : 159 - (o + (64 - a + i.val) * h) =
      159 - (o + 68 * h) + (a + j.val) * h := by
    dsimp [j]
    omega
  rw [eqn]
  exact blue j

/-- The second gap has only five or six blue points. -/
def H1 : Prop :=
  ∀ (R : ℕ → Prop) (p q u v : ℕ),
    (17 ≤ p ∧ p + 8 ≤ q ∧ q ≤ p + 13 ∧ p + q ≤ 159 ∧
      u + 6 ≤ v ∧ v ≤ u + 13 ∧ v < 160 ∧
      (q ≤ 62 → u + 7 ≤ v) ∧ (q ≤ 41 → u + 8 ≤ v)) →
    q < u → v < u + 8 →
    (p + u ≠ 2 * q ∧ p + v ≠ 2 * q ∧ p + v ≠ 2 * u ∧ q + v ≠ 2 * u) →
    (R p ∧ R q ∧ ∀ x, p < x → x < q → ¬ R x) →
    (R u ∧ R v ∧ ∀ x, u < x → x < v → ¬ R x) →
    (∀ o h : ℕ, 0 < h → o + 68 * h < 160 →
      ∃ a, a + 4 < 69 ∧ ∀ i : Fin 5, ¬ R (o + (a + i.val) * h)) →
    (∀ a d, 0 < d → a + 2 * d < 160 → R a → R (a + d) → R (a + 2 * d) → False) →
    (∀ a d, 0 < d → a + 12 * d < 160 → ∃ i : Fin 13, R (a + i.val * d)) →
    False

/-- The second gap is long enough to reverse, but its position prevents reversal. -/
def H2 : Prop :=
  ∀ (R : ℕ → Prop) (p q u v : ℕ),
    (17 ≤ p ∧ p + 8 ≤ q ∧ q ≤ p + 13 ∧ p + q ≤ 159 ∧
      u + 6 ≤ v ∧ v ≤ u + 13 ∧ v < 160 ∧
      (q ≤ 62 → u + 7 ≤ v) ∧ (q ≤ 41 → u + 8 ≤ v)) →
    q < u → u + 8 ≤ v → (u + v < 159 ∨ 142 < v) →
    (p + u ≠ 2 * q ∧ p + v ≠ 2 * q ∧ p + v ≠ 2 * u ∧ q + v ≠ 2 * u) →
    (R p ∧ R q ∧ ∀ x, p < x → x < q → ¬ R x) →
    (R u ∧ R v ∧ ∀ x, u < x → x < v → ¬ R x) →
    (∀ o h : ℕ, 0 < h → o + 68 * h < 160 →
      ∃ a, a + 4 < 69 ∧ ∀ i : Fin 5, ¬ R (o + (a + i.val) * h)) →
    (∀ a d, 0 < d → a + 2 * d < 160 → R a → R (a + d) → R (a + 2 * d) → False) →
    (∀ a d, 0 < d → a + 12 * d < 160 → ∃ i : Fin 13, R (a + i.val * d)) →
    False

/-- Both orientations satisfy the endpoint bounds. Keep the one whose endpoint sum is at most 318. -/
def H3 : Prop :=
  ∀ (R : ℕ → Prop) (p q u v : ℕ),
    (17 ≤ p ∧ p + 8 ≤ q ∧ q ≤ p + 13 ∧ p + q ≤ 159 ∧
      u + 6 ≤ v ∧ v ≤ u + 13 ∧ v < 160 ∧
      (q ≤ 62 → u + 7 ≤ v) ∧ (q ≤ 41 → u + 8 ≤ v)) →
    q < u → u + 8 ≤ v → 159 ≤ u + v → v ≤ 142 → p + q + u + v ≤ 318 →
    (p + u ≠ 2 * q ∧ p + v ≠ 2 * q ∧ p + v ≠ 2 * u ∧ q + v ≠ 2 * u) →
    (R p ∧ R q ∧ ∀ x, p < x → x < q → ¬ R x) →
    (R u ∧ R v ∧ ∀ x, u < x → x < v → ¬ R x) →
    (∀ o h : ℕ, 0 < h → o + 68 * h < 160 →
      ∃ a, a + 4 < 69 ∧ ∀ i : Fin 5, ¬ R (o + (a + i.val) * h)) →
    (∀ a d, 0 < d → a + 2 * d < 160 → R a → R (a + d) → R (a + 2 * d) → False) →
    (∀ a d, 0 < d → a + 12 * d < 160 → ∃ i : Fin 13, R (a + i.val * d)) →
    False

theorem main : H1 → H2 → H3 → OMA.R_Green14_W_3_13_R3.H2 := by
  intro short boundary canonical R p q u v widths separated left right five free meets
  have shape : 17 ≤ p ∧ p + 8 ≤ q ∧ q ≤ p + 13 ∧ p + q ≤ 159 ∧
      u + 6 ≤ v ∧ v ≤ u + 13 ∧ v < 160 ∧
      (q ≤ 62 → u + 7 ≤ v) ∧ (q ≤ 41 → u + 8 ≤ v) := widths
  obtain ⟨hp, hpq, hq, hcenter, huv, hvu, hv, narrow, narrower⟩ := shape
  have noTriple := endpoint_exclusions (R := R) (by omega : p < q) separated
    (by omega : u < v) hv left right free
  by_cases hshort : v < u + 8
  · exact short R p q u v widths separated hshort noTriple left right five free meets
  have hlong : u + 8 ≤ v := by omega
  by_cases hboundary : u + v < 159 ∨ 142 < v
  · exact boundary R p q u v widths separated hlong hboundary noTriple left right five free meets
  have center : 159 ≤ u + v := by omega
  have margin : v ≤ 142 := by omega
  by_cases order : p + q + u + v ≤ 318
  · exact canonical R p q u v widths separated hlong center margin order noTriple
      left right five free meets
  let S (x : ℕ) := R (159 - x)
  let p' := 159 - v
  let q' := 159 - u
  let u' := 159 - q
  let v' := 159 - p
  have shape' : 17 ≤ p' ∧ p' + 8 ≤ q' ∧ q' ≤ p' + 13 ∧ p' + q' ≤ 159 ∧
      u' + 6 ≤ v' ∧ v' ≤ u' + 13 ∧ v' < 160 ∧
      (q' ≤ 62 → u' + 7 ≤ v') ∧ (q' ≤ 41 → u' + 8 ≤ v') := by
    dsimp [p', q', u', v']
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      fun _ ↦ by omega, fun _ ↦ by omega⟩
  have separated' : q' < u' := by dsimp [q', u']; omega
  have hlong' : u' + 8 ≤ v' := by dsimp [u', v']; omega
  have center' : 159 ≤ u' + v' := by dsimp [u', v']; omega
  have margin' : v' ≤ 142 := by dsimp [v']; omega
  have order' : p' + q' + u' + v' ≤ 318 := by dsimp [p', q', u', v']; omega
  have left' : S p' ∧ S q' ∧ ∀ x, p' < x → x < q' → ¬ S x :=
    reflect_gap (by omega : u < v) hv right
  have right' : S u' ∧ S v' ∧ ∀ x, u' < x → x < v' → ¬ S x :=
    reflect_gap (by omega : p < q) (by omega : q < 160) left
  have free' : ∀ a d, 0 < d → a + 2 * d < 160 →
      S a → S (a + d) → S (a + 2 * d) → False := reflect_free free
  have exclusions := endpoint_exclusions (R := S) (by have := shape'.2.1; omega)
    separated' (by omega) (by omega) left' right' free'
  exact canonical S p' q' u' v' shape' separated' hlong' center' margin' order'
    exclusions left' right' (reflect_five five) free' (reflect_meets meets)

end OMA.R_Green14_W_3_13_R3_H2_R1
