import FormalConjectures.ErdosProblems.«1066»
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-! Swanepoel, Independence Numbers of Planar Contact Graphs,
Discrete & Computational Geometry 28 (2002), §§3–4, DOI 10.1007/s00454-002-2897-y.
The first step extracts the length-13 boundary arc. The second proves the local Euclidean
angle charges. Neither asks for the original independent-set bound. -/

open Finset Real
open scoped EuclideanGeometry Topology
namespace OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R1

/-- Swanepoel's boundary-arc extraction for m=8. The origin of the turn array is p1. -/
def H1 : Prop := by
  classical
  exact
    let v : (EuclideanSpace ℝ (Fin 2)) → ℂ := fun x => ⟨x 0,x 1⟩
    let A : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2)) → ℝ := fun x y z =>
      let u := Complex.arg ((v z-v y)/(v x-v y))
      if u < 0 then u+2*π else u
    let G : Finset (EuclideanSpace ℝ (Fin 2)) → Prop := fun Y =>
      ∃ S ⊆ Y, (S : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => dist x y ≠ 1) ∧ 8*Y.card ≤ 31*S.card
    ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), (X : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => 1 ≤ dist x y) → ¬ G X →
      (∀ Y ⊆ X, Y.card < X.card → G Y) →
      ∃ (p q r s : ℕ → (EuclideanSpace ℝ (Fin 2))) (t : ℕ → ℝ),
      ((∀ i < 14, p i ∈ X) ∧
      (∀ i < 13, q i ∈ X) ∧
      (∀ i, 2 ≤ i → i ≤ 11 → r i ∈ X ∧ s i ∈ X) ∧
      (∀ i < 14, ∀ j < 14, p i = p j → i = j) ∧
      (∀ i < 13, dist (p i) (p (i+1))=1 ∧ dist (p i) (q i)=1 ∧
        dist (p (i+1)) (q i)=1 ∧ A (p (i+1)) (p i) (q i)=π/3) ∧
      (∀ i, 1 ≤ i → i ≤ 13 → (X.filter (fun z => dist (p i) z=1)).card=4) ∧
      (∀ i, 2 ≤ i → i ≤ 11 → ∀ j : Fin 6,
        dist (q i) (![s i,r i,q (i-1),p i,p (i+1),q (i+1)] j)=1) ∧
      (∀ i, 2 ≤ i → i ≤ 11 →
        StrictMono (fun j : Fin 6 => A (s i) (q i) (![s i,r i,q (i-1),p i,p (i+1),q (i+1)] j))) ∧
      (∀ i, 1 ≤ i → i ≤ 12 → t (i-1)=A (p (i+1)) (p i) (p (i-1))-π)) ∧
      (∀ k < 13, 0 ≤ t k) ∧ (∑ k ∈ range 13, t k < π/3) ∧
      (∀ a, 2 ≤ a → a < 6 → ¬ (∀ i, a ≤ i → i < a+3 → s i=r (i+1)))


/-- The two consequences of the Euclidean local charge calculation. -/
def H2 : Prop := by
  classical
  exact
    let v : (EuclideanSpace ℝ (Fin 2)) → ℂ := fun x => ⟨x 0,x 1⟩
    let A : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2)) → ℝ := fun x y z =>
      let u := Complex.arg ((v z-v y)/(v x-v y))
      if u < 0 then u+2*π else u
    ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), (X : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => 1 ≤ dist x y) →
      ∀ (p q r s : ℕ → (EuclideanSpace ℝ (Fin 2))) (t : ℕ → ℝ), ((∀ i < 14, p i ∈ X) ∧
      (∀ i < 13, q i ∈ X) ∧
      (∀ i, 2 ≤ i → i ≤ 11 → r i ∈ X ∧ s i ∈ X) ∧
      (∀ i < 14, ∀ j < 14, p i = p j → i = j) ∧
      (∀ i < 13, dist (p i) (p (i+1))=1 ∧ dist (p i) (q i)=1 ∧
        dist (p (i+1)) (q i)=1 ∧ A (p (i+1)) (p i) (q i)=π/3) ∧
      (∀ i, 1 ≤ i → i ≤ 13 → (X.filter (fun z => dist (p i) z=1)).card=4) ∧
      (∀ i, 2 ≤ i → i ≤ 11 → ∀ j : Fin 6,
        dist (q i) (![s i,r i,q (i-1),p i,p (i+1),q (i+1)] j)=1) ∧
      (∀ i, 2 ≤ i → i ≤ 11 →
        StrictMono (fun j : Fin 6 => A (s i) (q i) (![s i,r i,q (i-1),p i,p (i+1),q (i+1)] j))) ∧
      (∀ i, 1 ≤ i → i ≤ 12 → t (i-1)=A (p (i+1)) (p i) (p (i-1))-π)) →
      (∀ k < 13, 0 ≤ t k) → (∑ k ∈ range 13, t k < π/3) →
      (∀ i, 1 ≤ i → i < 10 → s (i+1) ≠ r (i+2) →
        π/3 ≤ t i+2*t (i+1)+t (i+2)) ∧
      (∀ i, 1 ≤ i → i < 9 → s (i+1) ≠ r (i+2) → s (i+2) ≠ r (i+3) →
        π/3 ≤ t i+t (i+1)+t (i+2)+t (i+3))


open scoped EuclideanGeometry Topology
open Finset



lemma exact_config (n : ℕ) : ∃ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n ∧
    (X : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y ↦ 1 ≤ dist x y) := by
  classical
  let f : ℕ → (EuclideanSpace ℝ (Fin 2)) := fun t => EuclideanSpace.single 0 (t : ℝ)
  have hf : Function.Injective f := by
    intro a b h
    have hv := congrArg (fun z : (EuclideanSpace ℝ (Fin 2)) => z 0) h
    have hc : (a : ℝ) = (b : ℝ) := by simpa [f, EuclideanSpace.single_apply] using hv
    exact_mod_cast hc
  refine ⟨(range n).image f, by rw [card_image_of_injective _ hf, card_range], ?_⟩
  intro x hx y hy hn
  obtain ⟨a, _, rfl⟩ := mem_image.mp (Finset.mem_coe.mp hx)
  obtain ⟨b, _, rfl⟩ := mem_image.mp (Finset.mem_coe.mp hy)
  have hab : a ≠ b := fun h => hn (congrArg f h)
  change (1 : ℝ) ≤ dist (EuclideanSpace.single (0 : Fin 2) (a : ℝ))
    (EuclideanSpace.single (0 : Fin 2) (b : ℝ))
  rw [EuclideanSpace.dist_single_same, Real.dist_eq]
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma graph_card_of_independent {X S : Finset (EuclideanSpace ℝ (Fin 2))} (hs : S ⊆ X)
    (hi : (S : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => dist x y ≠ 1)) :
    S.card ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
  classical
  let T : Finset ((X : Set (EuclideanSpace ℝ (Fin 2)))) := S.subtype (fun p => p ∈ (X : Set (EuclideanSpace ℝ (Fin 2))))
  have hT : (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).IsIndepSet
      (T : Set ((X : Set (EuclideanSpace ℝ (Fin 2))))) := by
    intro a ha b hb hab h
    have ha' : (a : (EuclideanSpace ℝ (Fin 2))) ∈ S := by simpa [T] using ha
    have hb' : (b : (EuclideanSpace ℝ (Fin 2))) ∈ S := by simpa [T] using hb
    exact hi ha' hb' (fun he => hab (Subtype.ext he)) h
  have hcard : T.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun p hp => Finset.mem_coe.mpr (hs hp))
  rw [← hcard]
  exact hT.card_le_indepNum

lemma ratio_of_finite_sets
    (h : ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), (X : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => 1 ≤ dist x y) →
      ∃ S ⊆ X, (S : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => dist x y ≠ 1) ∧ 8*X.card ≤ 31*S.card)
    (n : ℕ) : (8/31 : ℝ) * n ≤ Erdos1066.g n := by
  let V : Set ℕ := {m | ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n →
    (X : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => 1 ≤ dist x y) →
    m ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum}
  have hmem : (8*n+30)/31 ∈ V := by
    intro X hXn hx
    obtain ⟨S,hs,hi,hc⟩ := h X hx
    have hS := graph_card_of_independent hs hi
    omega
  have hbd : BddAbove V := by
    obtain ⟨X,hXn,hX⟩ := exact_config n
    exact ⟨_, fun m hm => hm X hXn hX⟩
  have hl : (8*n+30)/31 ≤ Erdos1066.g n := le_csSup hbd hmem
  have hnat : 8*n ≤ 31*Erdos1066.g n := by omega
  have hr : (8 : ℝ)*n ≤ 31*(Erdos1066.g n : ℝ) := by exact_mod_cast hnat
  linarith



open Finset

lemma turn_budget_one_failure (t : ℕ → ℝ) (aligned : ℕ → Prop) (L : ℝ)
    (hn : ∀ k < 13, 0 ≤ t k)
    (ht : ∑ k ∈ range 13, t k < L)
    (hfar : ∀ i < 10, ¬ aligned i → L ≤ t i + 2*t (i+1) + t (i+2))
    (hclose : ∀ i < 9, ¬ aligned i → ¬ aligned (i+1) →
        L ≤ t i + t (i+1) + t (i+2) + t (i+3)) :
    ∀ i j, i < 10 → j < 10 → ¬ aligned i → ¬ aligned j → i = j := by
  have no_pair : ∀ i j, i < j → j < 10 → ¬ aligned i → ¬ aligned j → False := by
    intro i j hij hj fi fj
    have hi : i < 10 := by omega
    by_cases e : j = i+1
    · have i9 : i < 9 := by omega
      have h4 := hclose i i9 fi (e ▸ fj)
      have h0 : i ∈ range 13 := mem_range.mpr (by omega)
      have h1 : i+1 ∈ range 13 := mem_range.mpr (by omega)
      have h2 : i+2 ∈ range 13 := mem_range.mpr (by omega)
      have h3 : i+3 ∈ range 13 := mem_range.mpr (by omega)
      have few : t i + t (i+1) + t (i+2) + t (i+3) ≤ ∑ k ∈ range 13, t k := by
        calc
          _ = ∑ k ∈ range 13,
            ((if k=i then t k else 0) + (if k=i+1 then t k else 0) +
             (if k=i+2 then t k else 0) + (if k=i+3 then t k else 0)) := by
            simp [sum_add_distrib,Finset.sum_ite_eq',h0,h1,h2,h3]
          _ ≤ _ := sum_le_sum fun k hk => by
            have kp := hn k (mem_range.mp hk)
            split_ifs <;> first | omega | linarith
      linarith
    · have sep : i+2 ≤ j := by omega
      let w (a k : ℕ) : ℝ :=
        (if k=a then t k else 0) + (if k=a+1 then 2*t k else 0) +
        (if k=a+2 then t k else 0)
      have W (a : ℕ) (ha : a < 10) :
          (∑ k ∈ range 13, w a k) = t a + 2*t (a+1) + t (a+2) := by
        have h0 : a ∈ range 13 := mem_range.mpr (by omega)
        have h1 : a+1 ∈ range 13 := mem_range.mpr (by omega)
        have h2 : a+2 ∈ range 13 := mem_range.mpr (by omega)
        simp [w,sum_add_distrib,Finset.sum_ite_eq',h0,h1,h2]
      have cap : (∑ k ∈ range 13, (w i k + w j k)) ≤
          ∑ k ∈ range 13, 2*t k := by
        apply sum_le_sum
        intro k hk
        have kp := hn k (mem_range.mp hk)
        dsimp [w]
        split_ifs <;> first | omega | linarith
      rw [sum_add_distrib, W i hi, W j hj, ← mul_sum] at cap
      linarith [hfar i hi fi,hfar j hj fj]
  intro i j hi hj fi fj
  by_contra ne
  rcases lt_or_gt_of_ne ne with h|h
  · exact no_pair i j h hj fi fj
  · exact no_pair j i h hi fj fi



open Finset

/-- The two test triples start at zero-based indices 1 and 4, so both are
legitimate even when no neighbor pair was supplied at index 0. -/
lemma shifted_early_triplet (t : ℕ→ℝ) (c : ℕ→Prop) (L : ℝ)
    (hpos : ∀ k < 13, 0 ≤ t k) (hbudget : ∑ k ∈ range 13, t k < L)
    (hfar : ∀ i, 1 ≤ i → i < 10 → ¬ c i → L≤t i+2*t (i+1)+t (i+2))
    (hclose : ∀ i, 1 ≤ i → i < 9 → ¬ c i → ¬ c (i+1) →
      L≤t i+t (i+1)+t (i+2)+t (i+3)) :
    ∃ a : ℕ, (a=1 ∨ a=4) ∧ ∀ i, a ≤ i → i < a+3 → c i := by
  let D (i : ℕ) := i=0 ∨ c i
  have HF : ∀ i < 10, ¬ D i → L≤t i+2*t (i+1)+t (i+2) := by
    intro i hi hn
    exact hfar i (by by_contra! h0; exact hn (Or.inl (by omega))) hi
      (fun h => hn (Or.inr h))
  have HA : ∀ i < 9, ¬ D i → ¬ D (i+1) → L≤t i+t (i+1)+t (i+2)+t (i+3) := by
    intro i hi hn hm
    exact hclose i (by by_contra! h0; exact hn (Or.inl (by omega))) hi
      (fun h => hn (Or.inr h)) (fun h => hm (Or.inr h))
  have hOne := turn_budget_one_failure t D L hpos hbudget HF HA
  by_cases hFirst : ∀ i, 1 ≤ i → i < 4 → c i
  · exact ⟨1,Or.inl rfl,hFirst⟩
  · push Not at hFirst
    obtain ⟨j,hj1,hj4,hjbad⟩ := hFirst
    refine ⟨4,Or.inr rfl,?_⟩
    intro i hi1 hi2
    by_contra hb
    have hiD : ¬ D i := by
      intro hx
      rcases hx with e | hc
      · omega
      · exact hb hc
    have hjD : ¬ D j := by
      intro hx
      rcases hx with e | hc
      · omega
      · exact hjbad hc
    have h := hOne i j (by omega) (by omega) hiD hjD
    omega


theorem main : H1 → H2 → type_of% @Erdos1066.erdos_1066.variants.swanepoel := by
  classical
  intro h1 h2
  unfold H1 at h1
  unfold H2 at h2
  apply ratio_of_finite_sets
  intro X hX
  by_contra hx
  let good : Finset (EuclideanSpace ℝ (Fin 2)) → Prop := fun Y =>
    ∃ S ⊆ Y, (S : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => dist x y ≠ 1) ∧ 8*Y.card ≤ 31*S.card
  let Q (n : ℕ) : Prop := ∃ Y : Finset (EuclideanSpace ℝ (Fin 2)), Y.card=n ∧
    (Y : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun a b => 1≤dist a b) ∧ ¬ good Y
  have hQ : ∃ n, Q n := ⟨X.card,X,rfl,hX,hx⟩
  obtain ⟨Y,hY,hSep,hBad⟩ := Nat.find_spec hQ
  have hSmall : ∀ Z ⊆ Y, Z.card < Y.card → good Z := by
    intro Z hsub hlt
    by_contra hn
    have hsub' : (Z : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Y := by exact_mod_cast hsub
    have hZ : Q Z.card := ⟨Z,rfl,hSep.mono hsub',hn⟩
    have hmin := Nat.find_min' hQ hZ
    omega
  obtain ⟨p,q,r,s,t,hArc,hN,hBudget,hNo⟩ := h1 Y hSep hBad hSmall
  obtain ⟨hFar,hNear⟩ := h2 Y hSep p q r s t hArc hN hBudget
  obtain ⟨a,ha,hTriple⟩ := shifted_early_triplet t (fun i => s (i+1)=r (i+2))
    (π/3) hN hBudget hFar hNear
  have ha' : 2 ≤ a+1 ∧ a+1 < 6 := by rcases ha with h|h <;> omega
  apply hNo (a+1) ha'.1 ha'.2
  intro i hi hilt
  have H := hTriple (i-1) (by omega) (by omega)
  rwa [show i-1+1=i by omega,show i-1+2=i+1 by omega] at H

end OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R1
