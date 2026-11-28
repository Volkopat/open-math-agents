import OMAReductions.R_oeis_a046747_R1
import Mathlib

/-!
# Row exposure for the singularity probability of a Boolean matrix

Remove the zero-row, zero-column and duplicate-row and duplicate-column events.
Their total union has cardinality at most the proposed leading term times the size
of the sample space. Exposing all but one row reduces the remaining count to two
rectangular estimates. With independent exposed rows, one counts Boolean vectors
in their real span that separate every pair of exposed columns still identical.

The coordinate deletion count also appears in grp06's lower-bound PR #26455.
See Hu, Song and Wu, arXiv:2609.39463v2, Corollary 1.2 for the asymptotic.
-/
namespace OMA.R_oeis_a046747_R1_H2_R1
open Finset Filter
open scoped Classical

/-- Delete the coordinate forced to be a given function of the remaining coordinates. -/
lemma card_forced {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (j : Fin n)
    (g : ({t : Fin n // t ≠ j} → X) → X) :
    (univ.filter fun f : Fin n → X => f j = g (fun t => f t.val)).card =
      Fintype.card X ^ (n-1) := by
  classical
  rw [← Fintype.card_subtype]
  let e : {f : Fin n → X // f j = g (fun t => f t.val)} ≃ ({t : Fin n // t ≠ j} → X) :=
    { toFun := fun f t => f.val t.val
      invFun := fun h => ⟨fun i => if hi : i = j then g h else h ⟨i,hi⟩, by
        simp
        exact congrArg g (funext fun t => by simp [t.property])⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        by_cases hi : i = j
        · subst i
          simpa using f.property.symm
        · simp [hi]
      right_inv := by intro h; funext t; simp [t.property] }
  simpa using Fintype.card_congr e

/-- Union bound for one zero coordinate or a collision of two coordinates. -/
lemma bad_family {X : Type*} [Fintype X] [DecidableEq X] (z : X) (n : ℕ) :
    (univ.filter fun f : Fin n → X => ¬ (Function.Injective f ∧ ∀ i, f i ≠ z)).card ≤
      (n+1).choose 2 * Fintype.card X ^ (n-1) := by
  classical
  let P := {p : Fin n × Fin n // p.1 < p.2}
  let Z (i : Fin n) := univ.filter fun f : Fin n → X => f i = z
  let C (p : P) := univ.filter fun f : Fin n → X => f p.val.2 = f p.val.1
  have cZ (i : Fin n) : (Z i).card = Fintype.card X^(n-1) := card_forced i (fun _ => z)
  have cC (p : P) : (C p).card = Fintype.card X^(n-1) :=
    card_forced p.val.2 (fun h => h ⟨p.val.1,p.property.ne⟩)
  have cover : (univ.filter fun f : Fin n → X => ¬ (Function.Injective f ∧ ∀ i, f i ≠ z)) ⊆
      univ.biUnion Z ∪ univ.biUnion C := by
    intro f hf
    have h := (mem_filter.mp hf).2
    by_cases inj : Function.Injective f
    · have zero : ∃ i, f i = z := by by_contra! hh; exact h ⟨inj,hh⟩
      obtain ⟨i,hi⟩ := zero
      exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,hi⟩⟩)
    · obtain ⟨i,j,eq,ne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
        simpa only [Function.Injective, not_forall, exists_prop] using inj
      apply mem_union_right
      rcases lt_or_gt_of_ne ne with hij | hji
      · exact mem_biUnion.mpr ⟨⟨(i,j),hij⟩,mem_univ _,mem_filter.mpr ⟨mem_univ _,eq.symm⟩⟩
      · exact mem_biUnion.mpr ⟨⟨(j,i),hji⟩,mem_univ _,mem_filter.mpr ⟨mem_univ _,eq⟩⟩
  have cardP : Fintype.card P = n.choose 2 := by
    dsimp [P]
    rw [Fintype.card_subtype, Fintype.card_product_filter_lt]
    simp
  apply (card_le_card cover).trans
  apply (card_union_le ..).trans
  apply (Nat.add_le_add (card_biUnion_le ..) (card_biUnion_le ..)).trans
  simp only [cZ, cC, sum_const, card_univ, Fintype.card_fin, cardP, nsmul_eq_mul, Nat.cast_id,
    Nat.choose_succ_succ, Nat.choose_one_right, add_mul]
  rfl

lemma elementary (n : ℕ) :
    let good (f : Fin n → Fin n → Bool) := Function.Injective f ∧ ∀ i, f i ≠ fun _ => false
    (univ.filter fun A : Fin n → Fin n → Bool => ¬(good A ∧ good (fun i j => A j i))).card ≤
      2 * (n+1).choose 2 * 2^(n*(n-1)) := by
  classical
  intro good
  let row := univ.filter fun A : Fin n → Fin n → Bool => ¬good A
  let col := univ.filter fun A : Fin n → Fin n → Bool => ¬good (fun i j => A j i)
  have cover : (univ.filter fun A : Fin n → Fin n → Bool => ¬(good A ∧ good (fun i j => A j i)))
      ⊆ row ∪ col := by
    intro A h
    rcases not_and_or.mp (mem_filter.mp h).2 with hr | hc
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hr⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hc⟩)
  have hrow : row.card ≤ (n+1).choose 2 * 2^(n*(n-1)) := by
    simpa [row,good,←pow_mul] using bad_family (fun _ : Fin n => false) n
  have hcol : col.card = row.card := by
    apply card_bij' (fun A _ i j => A j i) (fun A _ i j => A j i)
    · intro A _; rfl
    · intro A _; rfl
    · intro A h; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩
    · intro A h; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩
  apply (card_le_card cover).trans (card_union_le .. |>.trans ?_)
  rw [hcol]
  calc
    _ ≤ _ := Nat.add_le_add hrow hrow
    _ = _ := by ring

open OMA.S_oeis_a046747

open scoped Classical

lemma expose (n : ℕ) :
    let Row := Fin (n+1) → Bool
    let embed (r : Row) : Fin (n+1) → ℝ := fun j => if r j then 1 else 0
    let dependent := univ.filter fun B : Fin n → Row =>
      (Function.Injective B ∧ ∀ i, B i ≠ fun _ => false) ∧
        ¬ LinearIndependent ℝ (fun i => embed (B i))
    let independent := univ.filter fun B : Fin n → Row =>
      LinearIndependent ℝ (fun i => embed (B i))
    let hits (B : Fin n → Row) := univ.filter fun y : Row =>
      y ≠ (fun _ => false) ∧ (∀ i, y ≠ B i) ∧
      embed y ∈ Submodule.span ℝ (Set.range (fun i => embed (B i))) ∧
      (∀ j, (∀ i, B i j = false) → y j = true) ∧
      ∀ j k, j ≠ k → (∀ i, B i j = B i k) → y j ≠ y k
    a (n+1) ≤ (2 * (n+2).choose 2 * 2^((n+1)*n) : ℕ) +
      (dependent.card * 2^(n+1) + ∑ B ∈ independent, (hits B).card) := by
  classical
  intro Row embed dependent independent hits
  let good (A : Fin (n+1) → Row) := Function.Injective A ∧ ∀ i, A i ≠ fun _ => false
  let bad := univ.filter fun A : Matrix (Fin (n+1)) (Fin (n+1)) Bool =>
    ¬ (good A ∧ good A.transpose)
  let sing := univ.filter fun A : Matrix (Fin (n+1)) (Fin (n+1)) Bool =>
    (A.map fun b => if b then (1 : ℝ) else 0).det = 0
  let clean := sing \ bad
  have hb : bad.card ≤ (2 * (n+2).choose 2 * 2^((n+1)*n) : ℕ) := by
    let F := univ.filter fun A : Fin (n+1) → Fin (n+1) → Bool =>
      ¬ (good A ∧ good (fun i j => A j i))
    have equal : bad.card = F.card := by
      dsimp only [bad,F]
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.refl _)
    rw [equal]
    exact elementary (n+1)
  let encode (A : Matrix (Fin (n+1)) (Fin (n+1)) Bool) : Σ _ : Fin n → Row, Row :=
    ⟨fun i => A i.succ, A 0⟩
  have enc_inj : Function.Injective encode := by
    intro A B h
    have tail := congrArg Sigma.fst h
    have head := congrArg (fun s : Σ _ : Fin n → Row, Row => s.2) h
    funext i
    exact Fin.cases head (fun j => congrFun tail j) i
  have bound : clean.card ≤ (dependent.sigma (fun _ => (univ : Finset Row)) ∪ independent.sigma hits).card := by
    refine card_le_card_of_injOn encode ?_ enc_inj.injOn
    intro A hA
    obtain ⟨hs,hn⟩ := mem_sdiff.mp hA
    have hdet := (mem_filter.mp hs).2
    have hg : good A ∧ good A.transpose := by
      by_contra h
      apply hn
      simpa only [bad, mem_filter, mem_univ, true_and] using h
    let B (i : Fin n) : Row := A i.succ
    by_cases hi : LinearIndependent ℝ (fun i => embed (B i))
    · apply mem_union_right
      apply mem_sigma.mpr
      refine ⟨mem_filter.mpr ⟨mem_univ _, hi⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
      refine ⟨hg.1.2 0, fun i h => Fin.succ_ne_zero i (hg.1.1 h.symm), ?_, ?_, ?_⟩
      · by_contra hout
        have allrows := linearIndependent_finCons.mpr ⟨hi,hout⟩
        let M := A.map fun b => if b then (1 : ℝ) else 0
        have eq : Fin.cons (embed (A 0)) (fun i => embed (B i)) = M.row := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        rw [eq] at allrows
        exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp allrows)).ne_zero hdet
      · intro j hj
        by_contra! h
        apply hg.2.2 j
        funext i
        exact Fin.cases (by simpa using h) (fun i => hj i) i
      · intro j k hjk he hy
        apply hjk
        apply hg.2.1
        funext i
        exact Fin.cases hy (fun i => he i) i
    · apply mem_union_left
      apply mem_sigma.mpr
      refine ⟨mem_filter.mpr ⟨mem_univ _, ⟨?_,fun i => hg.1.2 i.succ⟩, hi⟩, mem_univ _⟩
      exact fun _ _ h => Fin.succ_injective _ (hg.1.1 h)
  have count := bound.trans (card_union_le ..)
  simp only [card_sigma, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, Row] at count
  have split : sing.card ≤ bad.card + clean.card := by
    apply (card_le_card (show sing ⊆ bad ∪ clean by
      intro x hx
      by_cases h : x ∈ bad
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hx,h⟩))).trans (card_union_le ..)
  exact split.trans (Nat.add_le_add hb count)

/-- A rectangular matrix with distinct nonzero rows can still have a row dependency. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    let Row := Fin (n+1) → Bool
    let embed (r : Row) : Fin (n+1) → ℝ := fun j => if r j then 1 else 0
    let dependent := univ.filter fun B : Fin n → Row =>
      (Function.Injective B ∧ ∀ i, B i ≠ fun _ => false) ∧
        ¬ LinearIndependent ℝ (fun i => embed (B i))
    ((dependent.card * 2^(n+1) : ℕ) : ℝ) ≤ ε * (2 * (n+2).choose 2 * 2^((n+1)*n) : ℕ)

/-- Average number of new Boolean vectors in the span of an independent rectangular
matrix, with the final bit distinguishing columns that agree on its exposed rows. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    let Row := Fin (n+1) → Bool
    let embed (r : Row) : Fin (n+1) → ℝ := fun j => if r j then 1 else 0
    let independent := univ.filter fun B : Fin n → Row =>
      LinearIndependent ℝ (fun i => embed (B i))
    let hits (B : Fin n → Row) := univ.filter fun y : Row =>
      y ≠ (fun _ => false) ∧ (∀ i, y ≠ B i) ∧
      embed y ∈ Submodule.span ℝ (Set.range (fun i => embed (B i))) ∧
      (∀ j, (∀ i, B i j = false) → y j = true) ∧
      ∀ j k, j ≠ k → (∀ i, B i j = B i k) → y j ≠ y k
    ((∑ B ∈ independent, (hits B).card : ℕ) : ℝ) ≤ ε * (2 * (n+2).choose 2 * 2^((n+1)*n) : ℕ)

/-- The parent normalizer times the size of the sample space, in dimension n+1. -/
lemma mass_identity (n : ℕ) :
    (2:ℝ)^((n+1)^2) * (((n+2).choose 2 : ℝ) * (1/2)^n) =
      ((2 * (n+2).choose 2 * 2^((n+1)*n) : ℕ) : ℝ) := by
  push_cast
  rw [show (n+1)^2 = ((n+1)*n+1)+n by ring, pow_add, pow_succ, one_div_pow]
  field_simp

theorem main : H1 → H2 → OMA.R_oeis_a046747_R1.H2 := by
  intro hrect hspan ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((hrect (ε/2) (by positivity)).and (hspan (ε/2) (by positivity)))
  apply eventually_atTop.mpr
  refine ⟨N+1, ?_⟩
  intro m hm
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨hr,hs⟩ := hN n (by omega)
  have combine (D E I s : ℕ) (h : s ≤ D+(E+I))
      (he : (E:ℝ) ≤ ε/2*D) (hi : (I:ℝ) ≤ ε/2*D) : (s:ℝ) ≤ (1+ε)*D := by
    have hh : (s:ℝ) ≤ (D:ℝ)+((E:ℝ)+(I:ℝ)) := by exact_mod_cast h
    linarith
  have hc := combine _ _ _ _ (expose n) hr hs
  have hchoose : 0 < ((n+2).choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n+2)
  change ((a (n+1) : ℝ) / 2^((n+1)^2)) / (((n+2).choose 2 : ℝ)*(1/2)^n) ≤ 1+ε
  apply (div_le_iff₀ (by positivity)).mpr
  apply (div_le_iff₀ (by positivity)).mpr
  rw [← mass_identity] at hc
  linarith only [hc]
end OMA.R_oeis_a046747_R1_H2_R1
