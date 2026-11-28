import OMAStatements.S_mo_377545

/-!
Write m for the homotopy degree and s = m - n for the stem. The first
three inputs record consequences of published topology. The fourth is
the outstanding exclusion, with both degrees and residues restricted.

For S³ in degree m > 3, Curtis gives 2-torsion outside residues 1 and 2
modulo 8. In those two residues, use Gray's family in degree 4j+1 for
j ≥ 2 and Toda's 3-primary family in degree 4j+2 for j ≥ 1.
The complex Hopf fibration identifies the higher groups of S² with
those of S³. The quaternionic Hopf fibration surjects from πₘ(S⁴) onto
πₘ₋₁(S³), since its fiber inclusion into S⁷ is nullhomotopic.
Mahowald and Mori give 2-torsion above the diagonal for S⁵.
https://doi.org/10.4310/HHA.2016.v18.n2.a18

In stems 20 through 50, Baer's Tables 2–5 give a positive lower
bound for the 2-primary order exponent at every printed strictly
unstable finite entry with n ≥ 6. The one missing pair (s,n) = (50,51)
surjects by suspension onto the nonzero 2-primary stable 50-stem.
The stable stems through 90 with vanishing 2-part are 4, 5, 12, 13,
29 and 61. Their integral groups are trivial or cyclic of order 3.
https://arxiv.org/abs/2609.23984
https://doi.org/10.1007/s10240-023-00139-1

For s congruent to 0, 1 or 2 modulo 8, Curtis's table on p. 543 gives
2-primary classes with nonzero stabilizations already on S³. For s
congruent to 3 modulo 4, use the nonzero stabilizations of the
3-primary Toda elements on S³. These classes persist on larger spheres.
https://doi.org/10.1090/S0002-9904-1969-12236-6
-/

namespace OMA.R_mo_377545_R1

open OMA.S_mo_377545

-- Nat.card is zero on infinite groups, so divisibility by 2 also covers those.
def H1 : Prop :=
  ∀ (n k : ℕ) (x : Sphere n), 1 ≤ n → n ≤ 5 →
    let c := Nat.card (HomotopyGroup.Pi (k + 1) (Sphere n) x)
    c = 1 ∨ 2 ∣ c ∨ 3 ∣ c

-- Connectivity below the diagonal, Toda's integral table, Baer's 2-primary
-- bounds (Tables 2–5), and Isaksen--Wang--Xu's stable stems through 90.
def H2 : Prop :=
  ∀ (n k : ℕ) (x : Sphere n), 6 ≤ n →
    (k + 1 ≤ n + 50 ∨ (k + 1 ≤ n + 90 ∧ k + 1 ≤ 2 * n - 2)) →
    let c := Nat.card (HomotopyGroup.Pi (k + 1) (Sphere n) x)
    c = 1 ∨ 2 ∣ c ∨ 3 ∣ c

-- Above the tabulated range, count elements detected by stable classes.
-- Curtis, Table on p. 543 and §6. The Toda classes at 3 cover stems 3 mod 4.
def H3 : Prop :=
  ∀ (n k : ℕ) (x : Sphere n), let s := k + 1 - n
    6 ≤ n → 50 < s →
    (s % 8 ≤ 3 ∨ s % 8 = 7) →
    ∃ a : HomotopyGroup.Pi (k + 1) (Sphere n) x, orderOf a = 2 ∨ orderOf a = 3

-- Remaining question in three congruence classes. In these degrees, does
-- a class of prime order p > 3 always generate a proper cyclic subgroup?
def H4 : Prop :=
  ∀ (n k p : ℕ) (x : Sphere n), let s := k + 1 - n
    6 ≤ n → 50 < s →
    (s < n - 1 → 90 < s) → 4 ≤ s % 8 → s % 8 ≤ 6 → p.Prime → 3 < p →
    ∀ a : HomotopyGroup.Pi (k + 1) (Sphere n) x, orderOf a = p →
      Subgroup.zpowers a ≠ ⊤

lemma finite_sphere_zero : Finite (Sphere 0) := by
  classical
  have coordinate (v : EuclideanSpace ℝ (Fin 1)) (h : v ∈ Metric.sphere 0 1) :
      v 0 = 1 ∨ v 0 = -1 := by
    rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one] at h
    change (∑ i, v i ^ 2) = 1 ^ 2 at h
    rw [Fin.sum_univ_one] at h
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h
  apply Finite.of_injective (fun x : Sphere 0 => decide (x.val 0 = 1))
  intro x y h
  apply Subtype.ext
  ext i
  have hi : i = 0 := Fin.ext (by omega)
  subst i
  rcases coordinate x.val x.property with hx | hx <;>
    rcases coordinate y.val y.property with hy | hy <;>
    simp_all

lemma sphere_zero_card (k : ℕ) (x : Sphere 0) :
    Nat.card (HomotopyGroup.Pi (k + 1) (Sphere 0) x) = 1 := by
  let _ := finite_sphere_zero
  have constant (f : GenLoop (Fin (k + 1)) (Sphere 0) x) :
      f = GenLoop.const := by
    apply GenLoop.ext
    intro t
    exact (TotallyDisconnectedSpace.eq_of_continuous f f.val.continuous t 0).trans
      (GenLoop.boundary f 0 ⟨0, Or.inl rfl⟩)
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨?_⟩, inferInstance⟩
  intro a b
  induction a using Quotient.inductionOn with
  | _ f =>
    induction b using Quotient.inductionOn with
    | _ g => exact congrArg Quotient.mk' ((constant f).trans (constant g).symm)

lemma impossible_card {p c : ℕ} (hp : p.Prime) (hlt : 3 < p)
    (h : c = 1 ∨ 2 ∣ c ∨ 3 ∣ c) : c ≠ p := by
  rintro rfl
  rcases h with h | h | h
  · omega
  · have := hp.eq_one_or_self_of_dvd 2 h
    omega
  · have := hp.eq_one_or_self_of_dvd 3 h
    omega

lemma remaining_of_conjecture (h : type_of% @OMA.S_mo_377545.main) : H4 := by
  intro n k p x s _ _ _ _ _ hp hlt a ha hgen
  have generates := (Subgroup.zpowers a).eq_top_iff'.mp hgen
  have card := (orderOf_eq_card_of_forall_mem_zpowers generates).symm.trans ha
  exact h p hp hlt n k x ⟨(zmodMulEquivOfGenerator generates card).symm⟩

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_mo_377545.main := by
  intro low tables periodic remaining p hp hlt n k x
  rintro ⟨e⟩
  have card : Nat.card (HomotopyGroup.Pi (k + 1) (Sphere n) x) = p :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_zmod p)
  by_cases hz : n = 0
  · subst n
    rw [sphere_zero_card] at card
    omega
  by_cases hl : n ≤ 5
  · exact impossible_card hp hlt (low n k x (by omega) hl) card
  have hn : 6 ≤ n := by omega
  by_cases ht : k + 1 ≤ n + 50 ∨ (k + 1 ≤ n + 90 ∧ k + 1 ≤ 2 * n - 2)
  · exact impossible_card hp hlt (tables n k x hn ht) card
  let s := k + 1 - n
  have hs : 50 < s := by dsimp [s]; omega
  have hd : k + 1 = n + s := by dsimp [s]; omega
  have stable : s < n - 1 → 90 < s := by omega
  by_cases hr : s % 8 ≤ 3 ∨ s % 8 = 7
  · obtain ⟨a, ha⟩ := periodic n k x hn hs hr
    have divides := orderOf_dvd_natCard a
    exact impossible_card hp hlt (by
      rcases ha with h | h
      · exact Or.inr (Or.inl (h ▸ divides))
      · exact Or.inr (Or.inr (h ▸ divides))) card
  · let a := e.symm (Multiplicative.ofAdd (1 : ZMod p))
    have ha : orderOf a = p := by
      dsimp [a]
      rw [e.symm.orderOf_eq, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    apply remaining n k p x hn hs stable (by omega) (by omega) hp hlt a ha
    let _ : Finite (HomotopyGroup.Pi (k + 1) (Sphere n) x) :=
      Nat.finite_of_card_ne_zero (card.trans_ne hp.ne_zero)
    exact Subgroup.eq_top_of_card_eq _ ((Nat.card_zpowers a).trans (ha.trans card.symm))

end OMA.R_mo_377545_R1
