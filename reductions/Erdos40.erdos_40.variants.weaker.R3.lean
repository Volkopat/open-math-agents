import FormalConjectures.ErdosProblems.«40»
import Mathlib.Combinatorics.Schnirelmann

/-!
# Erdős 40 via the order of an additive basis

Adjoining 0 and 1 to a square-root-dense set with bounded two-sum counts gives
an additive basis of some finite order at a cost of at most four representations.
Thickening a set by a finite interval fills bounded gaps without increasing the
number of summands. The base case concerns three-term bases. The induction
step asks whether an example of order j+4 produces a set of the same density
with bounded two-sum counts and bounded gaps in its (j+3)-fold sumset.

Credit: @ubuwaits

The compactness argument through `weaker_iff_constant_one` is due to Nicholas
Wierenga (reduction R1, pull request 3739). It is included here because the
submission format requires a self-contained file.
-/

namespace OMA.R_Erdos40_erdos_40_variants_weaker_R3

section Compactness

open AdditiveCombinatorics Filter Real Set

theorem global_cap_of_limsup_ne_top (A : Set ℕ)
    (h : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤) :
    ∃ k : ℕ, ∀ n, sumRep A n ≤ k := by
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp h
  have hlt : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop < ((b + 1 : ℕ) : ℕ∞) := by
    rw [← hb]
    exact_mod_cast Nat.lt_succ_self b
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_limsup_lt hlt)
  refine ⟨max b ((Finset.range N).sup (sumRep A)), fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · have hb' : sumRep A n < b + 1 := by exact_mod_cast hN n hn
    exact (Nat.le_of_lt_succ hb').trans (le_max_left _ _)
  · exact (Finset.le_sup (f := sumRep A) (Finset.mem_range.mpr (by omega : n < N))).trans
      (le_max_right _ _)

theorem small_prefix (h : Erdos40.Erdos40For (fun _ ↦ 1)) (k : ℕ) (A : Set ℕ)
    (hcap : ∀ n, sumRep A n ≤ k) (L : ℕ) :
    ∃ n, L ≤ n ∧ (k : ℝ)^2 * ((A ∩ Icc 1 n).ncard : ℝ) < √(n : ℝ) := by
  by_contra! hnone
  have htop := h A (Asymptotics.IsBigO.of_bound ((k : ℝ)^2) (by
    filter_upwards [eventually_ge_atTop L] with n hn
    simpa only [div_one, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast]
      using hnone n hn))
  have hle : limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≤ (k : ℕ∞) :=
    limsup_le_of_le (h := Eventually.of_forall (fun n ↦ by exact_mod_cast hcap n))
  rw [htop] at hle
  exact (ENat.natCast_lt_top k).not_ge hle

theorem constant_one_of_witness {g : ℕ → ℝ} (hg : Tendsto g atTop atTop)
    (h : Erdos40.Erdos40For g) : Erdos40.Erdos40For (fun _ ↦ 1) := by
  intro A hA
  apply h A
  apply Asymptotics.IsBigO.trans _ hA
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [hg.eventually_ge_atTop 1] with n hn
  simpa only [div_one, one_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one hn))]
    using div_le_self (Real.sqrt_nonneg (n : ℝ)) hn

/-- A predicate determined by a finite prefix defines an open set of Boolean sequences. -/
theorem isOpen_prefix {P : (ℕ → Bool) → Prop} (n : ℕ)
    (hP : ∀ f g, (∀ i ≤ n, f i = g i) → (P f ↔ P g)) :
    IsOpen {f | P f} := by
  refine isOpen_pi_iff.mpr ?_
  intro f hf
  refine ⟨Finset.range (n + 1), fun i ↦ {f i}, fun i _ ↦ ⟨isOpen_discrete _, by simp⟩, ?_⟩
  intro g hg
  apply (hP f g ?_).mp hf
  intro i hi
  have hi' : i ∈ (↑(Finset.range (n + 1)) : Set ℕ) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  exact (Set.mem_singleton_iff.mp (Set.mem_pi.mp hg i hi')).symm

theorem sumRep_decode_congr {f g : ℕ → Bool} {n : ℕ}
    (h : ∀ i ≤ n, f i = g i) : sumRep (({i : ℕ | f i = true} : Set ℕ)) n = sumRep (({i : ℕ | g i = true} : Set ℕ)) n := by
  classical
  simp only [sumRep_def]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  by_cases hp : p ∈ _root_.Finset.HasAntidiagonal.antidiagonal n
  · have hsum := _root_.Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hleft : p.1 ≤ n := by omega
    have hright : p.2 ≤ n := by omega
    simp only [hp, true_and]
    change (f p.1 = true ∧ f p.2 = true) ↔ (g p.1 = true ∧ g p.2 = true)
    rw [h _ hleft, h _ hright]
  · simp [hp]

theorem count_decode_congr {f g : ℕ → Bool} {n : ℕ}
    (h : ∀ i ≤ n, f i = g i) :
    (({i : ℕ | f i = true} : Set ℕ) ∩ Icc 1 n).ncard = (({i : ℕ | g i = true} : Set ℕ) ∩ Icc 1 n).ncard := by
  have he : ({i : ℕ | f i = true} : Set ℕ) ∩ Icc 1 n = ({i : ℕ | g i = true} : Set ℕ) ∩ Icc 1 n := by
    ext i
    change (f i = true ∧ (1 ≤ i ∧ i ≤ n)) ↔ (g i = true ∧ (1 ≤ i ∧ i ≤ n))
    by_cases hi : i ≤ n
    · rw [h _ hi]
    · simp [hi]
  rw [he]

/-- Compactness makes the upper endpoint of the density failure window independent of the set. -/
theorem uniform_window (k L : ℕ)
    (hbad : ∀ A : Set ℕ, (∀ n, sumRep A n ≤ k) → ∀ l : ℕ,
      ∃ n, l ≤ n ∧ (k : ℝ)^2 * ((A ∩ Icc 1 n).ncard : ℝ) < Real.sqrt (n : ℝ)) :
    ∃ U : ℕ, ∀ A : Set ℕ, (∀ n, sumRep A n ≤ k) →
      ∃ n, L ≤ n ∧ n ≤ U ∧
        (k : ℝ)^2 * ((A ∩ Icc 1 n).ncard : ℝ) < Real.sqrt (n : ℝ) := by
  classical
  let K : Set (ℕ → Bool) := {f | ∀ n, sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k}
  have hK : IsCompact K := by
    apply IsClosed.isCompact
    have he : K = ⋂ n : ℕ, {f | sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k} := by
      ext f
      simp only [K, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [he]
    apply isClosed_iInter
    intro n
    apply isOpen_compl_iff.mp
    exact isOpen_prefix n fun f g h ↦ by
      change (¬ sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k) ↔ (¬ sumRep (({i : ℕ | g i = true} : Set ℕ)) n ≤ k)
      rw [sumRep_decode_congr h]
  let V : {n : ℕ // L ≤ n} → Set (ℕ → Bool) := fun n ↦
    {f | (k : ℝ)^2 * ((({i : ℕ | f i = true} : Set ℕ) ∩ Icc 1 n.val).ncard : ℝ) < Real.sqrt (n.val : ℝ)}
  have hV : ∀ n, IsOpen (V n) := by
    intro n
    apply isOpen_prefix n.val
    intro f g h
    rw [count_decode_congr h]
  have hcover : K ⊆ ⋃ n, V n := by
    intro f hf
    change ∀ n, sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k at hf
    obtain ⟨n, hn, hfail⟩ := hbad (({i : ℕ | f i = true} : Set ℕ)) hf L
    exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, hfail⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV hcover
  refine ⟨s.sup Subtype.val, ?_⟩
  intro A hA
  let f : ℕ → Bool := fun i ↦ decide (i ∈ A)
  have hf : ({i : ℕ | f i = true} : Set ℕ) = A := by
    ext i
    exact decide_eq_true_iff
  have hfK : f ∈ K := by
    change ∀ n, sumRep (({i : ℕ | f i = true} : Set ℕ)) n ≤ k
    simpa only [hf] using hA
  obtain ⟨n, hn, hfail⟩ := Set.mem_iUnion₂.mp (hs hfK)
  refine ⟨n.val, n.property, Finset.le_sup (f := Subtype.val) hn, ?_⟩
  change (k : ℝ)^2 * ((({i : ℕ | f i = true} : Set ℕ) ∩ Icc 1 n.val).ncard : ℝ) < Real.sqrt (n.val : ℝ) at hfail
  simpa only [hf] using hfail

/-- Uniform finite windows of low density give a single diverging witness function. -/
theorem diagonalWitness
    (hw : ∀ k L : ℕ, 0 < k → ∃ U : ℕ, ∀ A : Set ℕ,
      (∀ n, sumRep A n ≤ k) →
      ∃ n, L ≤ n ∧ n ≤ U ∧
        (k : ℝ)^2 * ((A ∩ Icc 1 n).ncard : ℝ) < Real.sqrt (n : ℝ))
    (hcap : ∀ A : Set ℕ,
      (limsup (fun n ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤) →
      ∃ k : ℕ, ∀ n, sumRep A n ≤ k) :
    ∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40.Erdos40For g := by
  classical
  choose U hU using fun j : ℕ => hw (j + 1) j (Nat.succ_pos j)
  -- The first window endpoint reaching n supplies its index.
  let endpoint (j : ℕ) := max j (U j)
  have reaches (n : ℕ) : ∃ j, n ≤ endpoint j := ⟨n, le_max_left _ _⟩
  let index (n : ℕ) := Nat.find (reaches n)
  let g (n : ℕ) : ℝ := (↑(index n + 1) : ℝ)
  have hgpos (n : ℕ) : 0 < g n := by
    dsimp [g]
    positivity
  refine ⟨g, ?_, ?_⟩
  · refine tendsto_atTop.2 fun x => ?_
    obtain ⟨j, hj⟩ := exists_nat_ge x
    filter_upwards [eventually_ge_atTop ((Finset.range j).sup endpoint + 1)] with n hn
    have hindex : j ≤ index n := by
      by_contra! hlt
      have hn' : n ≤ endpoint (index n) := Nat.find_spec (reaches n)
      have hend : endpoint (index n) ≤ (Finset.range j).sup endpoint :=
        Finset.le_sup (Finset.mem_range.mpr hlt)
      omega
    have hcast : (j : ℝ) ≤ g n := by
      dsimp [g]
      exact_mod_cast (show j ≤ index n + 1 by omega)
    exact hj.trans hcast
  · intro A hbigO
    by_contra hr
    obtain ⟨k, hk⟩ := hcap A hr
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hbigO
    obtain ⟨L, hL⟩ := eventually_atTop.mp hC
    obtain ⟨c, hc⟩ := exists_nat_ge C
    let j := max k (max c L)
    have hkj : k ≤ j + 1 := by
      have : k ≤ j := le_max_left _ _
      omega
    have hcj : C ≤ (↑(j + 1) : ℝ) := by
      apply hc.trans
      have : c ≤ j := (le_max_left c L).trans (le_max_right k _)
      exact_mod_cast (show c ≤ j + 1 by omega)
    have hLj : L ≤ j := (le_max_right c L).trans (le_max_right k _)
    obtain ⟨n, hjn, hnU, hsmall⟩ := hU j A (fun n => (hk n).trans hkj)
    have hind : index n ≤ j :=
      Nat.find_min' (reaches n) (hnU.trans (le_max_right _ _))
    have hgj : g n ≤ (↑(j + 1) : ℝ) := by
      dsimp [g]
      exact_mod_cast (Nat.succ_le_succ hind)
    let a : ℝ := ((A ∩ Icc 1 n).ncard : ℝ)
    have ha : 0 ≤ a := by
      dsimp [a]
      positivity
    have hbound := hL n (hLj.trans hjn)
    change ‖Real.sqrt (n : ℝ) / g n‖ ≤ C * ‖a‖ at hbound
    rw [Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (hgpos n).le),
      Real.norm_of_nonneg ha] at hbound
    have hcoeff : C * g n ≤ (↑(j + 1) : ℝ)^2 := by
      rw [pow_two]
      exact (mul_le_mul_of_nonneg_right hcj (hgpos n).le).trans
        (mul_le_mul_of_nonneg_left hgj (Nat.cast_nonneg _))
    have hsqrt : Real.sqrt (n : ℝ) ≤ (↑(j + 1) : ℝ)^2 * a := by
      calc
        Real.sqrt (n : ℝ) ≤ (C * a) * g n := (div_le_iff₀ (hgpos n)).mp hbound
        _ = (C * g n) * a := by ring
        _ ≤ (↑(j + 1) : ℝ)^2 * a := mul_le_mul_of_nonneg_right hcoeff ha
    exact (not_lt_of_ge hsqrt) hsmall

/-- A single diverging denominator exists exactly when square-root lower density
forces unbounded two-sum representations. -/
theorem weaker_iff_constant_one :
    (∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40.Erdos40For g) ↔
      Erdos40.Erdos40For (fun _ ↦ 1) := by
  constructor
  · rintro ⟨g, hg, h⟩
    exact constant_one_of_witness hg h
  · intro h
    apply diagonalWitness _ global_cap_of_limsup_ne_top
    intro k L _
    exact uniform_window k L (small_prefix h k)

end Compactness

open Finset Set AdditiveCombinatorics Filter
open scoped Pointwise Classical

private theorem mem_entries {A : Set ℕ} {n x : ℕ} :
    x ∈ ((Finset.Ioc 0 n).filter (fun x ↦ x ∈ A)) ↔ 0 < x ∧ x ≤ n ∧ x ∈ A := by
  simp [and_assoc]

private theorem entries_card (A : Set ℕ) (n : ℕ) :
    (((Finset.Ioc 0 n).filter (fun x ↦ x ∈ A))).card = (A ∩ Set.Icc 1 n).ncard := by
  have he : (↑(((Finset.Ioc 0 n).filter (fun x ↦ x ∈ A))) : Set ℕ) = A ∩ Set.Icc 1 n := by
    ext x
    rw [Finset.mem_coe, mem_entries]
    exact ⟨fun h ↦ ⟨h.2.2,h.1,h.2.1⟩,fun h ↦ ⟨h.2.1,h.2.2,h.1⟩⟩
  rw [← he, Set.ncard_coe_finset]

private theorem entries_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    ((Finset.Ioc 0 n).filter (fun x ↦ x ∈ A)) ⊆ ((Finset.Ioc 0 n).filter (fun x ↦ x ∈ B)) := by
  intro x hx
  obtain ⟨hx, hn, ha⟩ := mem_entries.mp hx
  exact mem_entries.mpr ⟨hx, hn, h ha⟩

private theorem entries_succ {A : Set ℕ} {n : ℕ} (h : n+1 ∈ A) :
    (((Finset.Ioc 0 (n+1)).filter (fun x ↦ x ∈ A))).card = (((Finset.Ioc 0 n).filter (fun x ↦ x ∈ A))).card + 1 := by
  have he : ((Finset.Ioc 0 (n+1)).filter (fun x ↦ x ∈ A)) = insert (n+1) (((Finset.Ioc 0 n).filter (fun x ↦ x ∈ A))) := by
    ext x
    simp only [mem_entries, Finset.mem_insert]
    constructor
    · rintro ⟨hp, hb, ha⟩
      by_cases ht : x=n+1
      · exact Or.inl ht
      · exact Or.inr ⟨hp, by omega, ha⟩
    · rintro (rfl | ⟨hp, hb, ha⟩)
      · exact ⟨by omega, le_rfl, h⟩
      · exact ⟨hp, by omega, ha⟩
  rw [he, card_insert_of_notMem]
  simp

private theorem shifted_entries {V D : Set ℕ} {j n : ℕ} (hj : j ∈ V) (hn : j ≤ n) :
    (((Finset.Ioc 0 j).filter (fun x ↦ x ∈ V+D))).card + (((Finset.Ioc 0 (n-j)).filter (fun x ↦ x ∈ D))).card ≤ (((Finset.Ioc 0 n).filter (fun x ↦ x ∈ V+D))).card := by
  let T := (((Finset.Ioc 0 (n-j)).filter (fun x ↦ x ∈ D))).image (fun x ↦ j+x)
  have dis : Disjoint (((Finset.Ioc 0 j).filter (fun x ↦ x ∈ V+D))) T := by
    refine Finset.disjoint_left.mpr ?_
    intro y hy ht
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
    have := (mem_entries.mp hx).1
    have := (mem_entries.mp hy).2.1
    omega
  have sub : ((Finset.Ioc 0 j).filter (fun x ↦ x ∈ V+D)) ∪ T ⊆ ((Finset.Ioc 0 n).filter (fun x ↦ x ∈ V+D)) := by
    intro y hy
    rcases mem_union.mp hy with hv | ht
    · obtain ⟨hp,hb,ha⟩ := mem_entries.mp hv
      exact mem_entries.mpr ⟨hp,hb.trans hn,ha⟩
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
      obtain ⟨hp,hb,ha⟩ := mem_entries.mp hx
      exact mem_entries.mpr ⟨by omega, by omega, ⟨j,hj,x,ha,rfl⟩⟩
  have size : T.card = (((Finset.Ioc 0 (n-j)).filter (fun x ↦ x ∈ D))).card :=
    card_image_of_injective _ (fun x y eq ↦ Nat.add_left_cancel eq)
  simpa only [card_union_of_disjoint dis, size] using Finset.card_le_card sub

/-- The prefix form of Schnirelmann's addition inequality, including its
dependence on the actual number of points of the first set at the cutoff. -/
theorem prefix_sum_gain (V D : Set ℕ) (v0 : 0 ∈ V) (d0 : 0 ∈ D)
    {δ : ℝ} (quota : ∀ n : ℕ, δ*n ≤ ((D ∩ Set.Icc 1 n).ncard : ℝ)) (n : ℕ) :
    ((V ∩ Set.Icc 1 n).ncard : ℝ) + δ*(n-(V ∩ Set.Icc 1 n).ncard) ≤
      (( (V+D) ∩ Set.Icc 1 n).ncard : ℝ) := by
  simp only [← entries_card] at quota ⊢
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ k =>
      by_cases hit : k+1 ∈ V
      · have hitSum : k+1 ∈ V+D := ⟨k+1,hit,0,d0,by simp⟩
        have old := ih k (by omega)
        rw [entries_succ hit, entries_succ hitSum]
        push_cast
        linarith
      · let S := (Finset.Icc 0 k).filter (· ∈ V)
        have ne : S.Nonempty := ⟨0, mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,Nat.zero_le _⟩,v0⟩⟩
        let j := S.max' ne
        have memj : j ∈ S := max'_mem _ _
        obtain ⟨bound, hj⟩ := mem_filter.mp memj
        have jk : j ≤ k := (mem_Icc.mp bound).2
        have same : ((Finset.Ioc 0 (k+1)).filter (fun x ↦ x ∈ V)) = ((Finset.Ioc 0 j).filter (fun x ↦ x ∈ V)) := by
          ext x
          rw [mem_entries, mem_entries]
          constructor
          · rintro ⟨pos,hx,hv⟩
            have nk : x≠k+1 := fun eq ↦ hit (eq ▸ hv)
            exact ⟨pos, le_max' S x (mem_filter.mpr
              ⟨mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩,hv⟩),hv⟩
          · rintro ⟨pos,hx,hv⟩
            exact ⟨pos,by omega,hv⟩
        have add := shifted_entries (D:=D) (n:=k+1) hj (by omega)
        have prior := ih j (by omega)
        have gap := quota (k+1-j)
        rw [Nat.cast_sub (by omega : j ≤ k+1)] at gap
        rw [same]
        have addR : ((((Finset.Ioc 0 j).filter (fun x ↦ x ∈ V+D))).card : ℝ) + (((Finset.Ioc 0 (k+1-j)).filter (fun x ↦ x ∈ D))).card ≤
            (((Finset.Ioc 0 (k+1)).filter (fun x ↦ x ∈ V+D))).card := by exact_mod_cast add
        linarith

private theorem zero_in_sums {D : Set ℕ} (hd : 0 ∈ D) (i : ℕ) : 0 ∈ i • D := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul]; exact ⟨0,ih,0,hd,rfl⟩

/-- If the positive counts in every prefix are at least n/Q, exactly
2Q summands suffice to cover all the natural numbers. -/
theorem basis_of_prefix_quota (D : Set ℕ) (d0 : 0 ∈ D) {Q : ℕ} (qpos : 0 < Q)
    (quota : ∀ n : ℕ, n ≤ Q * (D ∩ Set.Icc 1 n).ncard) :
    D.IsAddBasisOfOrder (2*Q) := by
  classical
  let d : ℝ := (Q : ℝ)⁻¹
  have qR : (0:ℝ) < Q := by exact_mod_cast qpos
  have dp : 0 < d := inv_pos.mpr qR
  have dq : d*(Q:ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt qR)
  have lower (n : ℕ) : d*n ≤ ((D ∩ Set.Icc 1 n).ncard : ℝ) := by
    have hn : (n:ℝ) ≤ Q * ((D ∩ Set.Icc 1 n).ncard : ℝ) := by exact_mod_cast quota n
    calc _ ≤ d*((Q:ℝ) * ((D ∩ Set.Icc 1 n).ncard : ℝ)) := mul_le_mul_of_nonneg_left hn dp.le
         _ = _ := by rw [← mul_assoc,dq,one_mul]
  have grow (i : ℕ) (hi : i ≤ Q) (n : ℕ) :
      d*(i:ℝ)*n/2 ≤ (((i • D) ∩ Set.Icc 1 n).ncard : ℝ) := by
    induction i with
    | zero => simp
    | succ i ih =>
      let v : ℝ := ((i • D ∩ Set.Icc 1 n).ncard : ℝ)
      have step := prefix_sum_gain (i • D) D (zero_in_sums d0 i) d0 lower n
      change v + d*((n:ℝ)-v) ≤ _ at step
      rw [succ_nsmul]
      have old : d*(i:ℝ)*n/2 ≤ v := ih (by omega)
      have bound : d*((i:ℝ)+1) ≤ 1 := by
        calc _ ≤ d*(Q:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hi) dp.le
             _ = 1 := dq
      push_cast
      by_cases low : v ≤ n/2
      · nlinarith [mul_nonneg dp.le (sub_nonneg.mpr low)]
      · have vn : v ≤ n := by
          dsimp [v]
          rw [← entries_card]
          exact_mod_cast (show (((Finset.Ioc 0 n).filter (fun x ↦ x ∈ i • D))).card ≤ n by
            simpa using card_filter_le (Finset.Ioc 0 n) (· ∈ i • D))
        nlinarith [mul_nonneg dp.le (sub_nonneg.mpr vn),
          mul_le_mul_of_nonneg_right bound (Nat.cast_nonneg n)]
  have half : (1:ℝ)/2 ≤ schnirelmannDensity (Q • D) := by
    rw [le_schnirelmannDensity_iff]
    intro n hn
    apply (le_div_iff₀ (by exact_mod_cast hn)).mpr
    have h := grow Q le_rfl n
    rw [dq,one_mul,← entries_card] at h
    change 1/2*(n:ℝ) ≤ (((Finset.Ioc 0 n).filter (fun x ↦ x ∈ Q • D))).card
    linarith
  have all := add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
    (zero_in_sums d0 Q) (zero_in_sums d0 Q) (by linarith : 1 ≤
      schnirelmannDensity (Q • D) + schnirelmannDensity (Q • D))
  intro n
  simp [two_mul,add_nsmul,all]

/-- Ordered sums of the positive entries through m give a lower bound for
the positive part of the two-fold sumset through 2m. -/
theorem pairs_force_sumset (A : Set ℕ) {K : ℕ} (cap : ∀ s, sumRep A s ≤ K) (m : ℕ) :
    (A ∩ Set.Icc 1 m).ncard^2 ≤ K * ((A+A) ∩ Set.Icc 1 (2*m)).ncard := by
  classical
  let F := ((Finset.Ioc 0 m).filter (fun x ↦ x ∈ A))
  let S := ((Finset.Ioc 0 (2*m)).filter (fun x ↦ x ∈ A+A))
  let f (p : ℕ × ℕ) := p.1+p.2
  have maps (p : ℕ × ℕ) (hp : p ∈ F ×ˢ F) : f p ∈ S := by
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
    obtain ⟨px,bx,ax⟩ := mem_entries.mp hx
    obtain ⟨py,by',ay⟩ := mem_entries.mp hy
    exact mem_entries.mpr ⟨by dsimp [f]; omega,by dsimp [f]; omega,⟨_,ax,_,ay,rfl⟩⟩
  have fiber (s : ℕ) : ((F ×ˢ F).filter (fun p ↦ f p=s)).card ≤ K := by
    apply le_trans _ (cap s)
    rw [sumRep_def]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨both,he⟩ := mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp both
    exact mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr he,
      (mem_entries.mp hx).2.2,(mem_entries.mp hy).2.2⟩
  calc
    _ = (F ×ˢ F).card := by simp [F,entries_card,pow_two]
    _ = ∑ s ∈ S, ((F ×ˢ F).filter (fun p ↦ f p=s)).card :=
      card_eq_sum_card_fiberwise (fun p hp ↦ maps p hp)
    _ ≤ ∑ _s ∈ S, K := sum_le_sum (fun s _ ↦ fiber s)
    _ = _ := by simp [S,entries_card,Nat.mul_comm]

private theorem insert_cap (A : Set ℕ) (b s : ℕ) :
    sumRep (insert b A) s ≤ sumRep A s + 2 := by
  classical
  let P := (Finset.HasAntidiagonal.antidiagonal s).filter
    (fun p : ℕ × ℕ ↦ p.1 ∈ A ∧ p.2 ∈ A)
  let U : Finset (ℕ × ℕ) := {(b,s-b),(s-b,b)}
  have sub : ((Finset.HasAntidiagonal.antidiagonal s).filter
      (fun p : ℕ × ℕ ↦ p.1 ∈ insert b A ∧ p.2 ∈ insert b A)) ⊆ P ∪ U := by
    rintro ⟨x,y⟩ hp
    obtain ⟨anti,hx,hy⟩ := mem_filter.mp hp
    have eq : x+y=s := Finset.HasAntidiagonal.mem_antidiagonal.mp anti
    rcases Set.mem_insert_iff.mp hx with rfl | ax
    · exact Finset.mem_union_right _ (by simp [U, show s-x=y by omega])
    rcases Set.mem_insert_iff.mp hy with rfl | ay
    · exact Finset.mem_union_right _ (by simp [U, show s-y=x by omega])
    exact Finset.mem_union_left _ (mem_filter.mpr ⟨anti,ax,ay⟩)
  have size : U.card ≤ 2 := Finset.card_le_two
  rw [sumRep_def,sumRep_def]
  convert (Finset.card_le_card sub).trans ((Finset.card_union_le P U).trans
    (Nat.add_le_add_left size P.card)) using 1
  all_goals first | rfl | (apply congrArg Finset.card; ext p; simp only [Finset.mem_filter])

/-- Adjoining exactly 0 and 1 preserves the original counting lower bound
and increases the ordered cap by at most four. -/
theorem finite_basis_completion (A : Set ℕ) {K : ℕ} (cap : ∀ s, sumRep A s ≤ K)
    (dense : (fun n : ℕ ↦ Real.sqrt (n:ℝ)) =O[atTop]
      (fun n ↦ ((A ∩ Set.Icc 1 n).ncard : ℝ))) :
    (insert 0 (insert 1 A)).IsAddBasis ∧ ∀ s, sumRep (insert 0 (insert 1 A)) s ≤ K+4 := by
  classical
  let E := insert 0 (insert 1 A)
  let D := E+E
  have sub : A ⊆ E := fun x hx ↦ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx)
  have ez : 0 ∈ E := Set.mem_insert _ _
  have eo : 1 ∈ E := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have dz : 0 ∈ D := ⟨0,ez,0,ez,rfl⟩
  have do' : 1 ∈ D := ⟨0,ez,1,eo,rfl⟩
  have mono {a b : ℕ} (hb : 2*a ≤ b) :
      ((A+A) ∩ Set.Icc 1 (2*a)).ncard ≤ (D ∩ Set.Icc 1 b).ncard := by
    rw [← entries_card,← entries_card]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨px,bx,y,ay,z,az,he⟩ := mem_entries.mp hx
    exact mem_entries.mpr ⟨px,bx.trans hb,⟨y,sub ay,z,sub az,he⟩⟩
  obtain ⟨c, hpos, hc⟩ := dense.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc.bound
  obtain ⟨L,hL⟩ := exists_nat_ge c
  have localBound (m : ℕ) (hm : N ≤ m) : m ≤ L^2 * (A ∩ Set.Icc 1 m).ncard^2 := by
    have small := hN m hm
    simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast] at small
    have sm : Real.sqrt (m:ℝ) ≤ L * ((A ∩ Set.Icc 1 m).ncard : ℝ) :=
      small.trans (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg _))
    have sq := sq_le_sq' (by linarith [Real.sqrt_nonneg (m:ℝ)] :
      -(L * ((A ∩ Set.Icc 1 m).ncard : ℝ)) ≤ Real.sqrt (m:ℝ)) sm
    rw [Real.sq_sqrt (Nat.cast_nonneg _),mul_pow] at sq
    exact_mod_cast sq
  let Q := 1 + 2*N + 3*(L^2*K)
  have quota (n : ℕ) : n ≤ Q * (D ∩ Set.Icc 1 n).ncard := by
    by_cases hn : n=0
    · simp [hn]
    have one : 1 ≤ (D ∩ Set.Icc 1 n).ncard := by
      rw [← entries_card]
      exact Finset.card_pos.mpr ⟨1,mem_entries.mpr ⟨by decide,by omega,do'⟩⟩
    by_cases large : max (2*N) 2 ≤ n
    · have mN : N ≤ n/2 := by omega
      have la := localBound (n/2) mN
      have p := (pairs_force_sumset A cap (n/2)).trans
        (Nat.mul_le_mul_left K (mono (by omega : 2*(n/2) ≤ n)))
      calc
        n ≤ 3*(n/2) := by omega
        _ ≤ 3*(L^2*((A ∩ Set.Icc 1 (n/2)).ncard)^2) := Nat.mul_le_mul_left _ la
        _ ≤ 3*(L^2*(K*(D ∩ Set.Icc 1 n).ncard)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ p)
        _ ≤ _ := by dsimp [Q]; nlinarith
    · calc
        n ≤ Q := by dsimp [Q]; omega
        _ ≤ Q * (D ∩ Set.Icc 1 n).ncard := by simpa using Nat.mul_le_mul_left Q one
  have b := basis_of_prefix_quota D dz (by dsimp [Q]; omega : 0<Q) quota
  refine ⟨⟨(2*Q)*2,fun n ↦ ?_⟩,fun s ↦ ?_⟩
  · have he : (2*Q) • D = ((2*Q)*2) • E := calc
      _ = (2*Q) • (2 • E) := congrArg (fun S : Set ℕ ↦ (2*Q) • S) (two_nsmul E).symm
      _ = _ := by rw [Nat.mul_comm (2*Q) 2]; exact (mul_nsmul ..).symm
    exact he ▸ b n
  · have h0 := insert_cap (insert 1 A) 0 s
    have h1 := insert_cap A 1 s
    have := cap s
    omega

/-- It suffices, and is necessary, to settle bounded representations on
square-root-dense additive bases of finite order that contain 0 and 1. -/
theorem exists_denominator_iff_finite_bases :
    (∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ Erdos40.Erdos40For g) ↔
      ∀ B : Set ℕ, 0 ∈ B → 1 ∈ B → B.IsAddBasis →
        (fun n : ℕ ↦ Real.sqrt (n:ℝ)) =O[atTop] (fun n ↦ ((B ∩ Set.Icc 1 n).ncard : ℝ)) →
        limsup (fun n ↦ (sumRep B n : ℕ∞)) atTop = ⊤ := by
  rw [weaker_iff_constant_one]
  constructor
  · intro general B _ _ _ dense
    exact general B (by simpa using dense)
  · intro bases A dense
    by_contra failed
    obtain ⟨K,cap⟩ := global_cap_of_limsup_ne_top A failed
    have root : (fun n : ℕ ↦ Real.sqrt (n:ℝ)) =O[atTop]
        (fun n ↦ ((A ∩ Set.Icc 1 n).ncard : ℝ)) := by simpa using dense
    let B := insert 0 (insert 1 A)
    obtain ⟨basis,bounded⟩ := finite_basis_completion A cap root
    have transfer : (fun n : ℕ ↦ ((A ∩ Set.Icc 1 n).ncard : ℝ)) =O[atTop]
        (fun n ↦ ((B ∩ Set.Icc 1 n).ncard : ℝ)) := by
      apply Asymptotics.IsBigO.of_bound 1
      apply Eventually.of_forall
      intro n
      simp only [Real.norm_natCast,one_mul,← entries_card]
      exact_mod_cast Finset.card_le_card (entries_mono (B:=B)
        (fun x (hx : x∈A) ↦ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx)) n)
    have top := bases B (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      basis (root.trans transfer)
    have bound : limsup (fun n ↦ (sumRep B n : ℕ∞)) atTop ≤ (↑(K+4 : ℕ) : ℕ∞) :=
      limsup_le_of_le (h:=Eventually.of_forall (fun n ↦ by exact_mod_cast bounded n))
    exact (bound.trans_lt (ENat.natCast_lt_top _)).ne top

/-- Thickening by the possible offsets 0 through d costs at most
(d+1)^2 in the ordered representation bound. -/
theorem thickening_cap (B : Set ℕ) {K : ℕ} (cap : ∀ s, sumRep B s ≤ K) (d s : ℕ) :
    sumRep (B + Set.Iic d) s ≤ (d+1)^2*K := by
  classical
  let offsets := (Finset.range (d+1)) ×ˢ (Finset.range (d+1))
  let P (t : ℕ) := (Finset.HasAntidiagonal.antidiagonal t).filter
    (fun p : ℕ × ℕ ↦ p.1 ∈ B ∧ p.2 ∈ B)
  let shifted (u : ℕ × ℕ) := (P (s-(u.1+u.2))).image
    (fun p ↦ (p.1+u.1,p.2+u.2))
  rw [sumRep_def]
  have sub : ((Finset.HasAntidiagonal.antidiagonal s).filter
      (fun p : ℕ × ℕ ↦ p.1 ∈ B+Set.Iic d ∧ p.2 ∈ B+Set.Iic d)) ⊆
      offsets.biUnion shifted := by
    rintro ⟨x,y⟩ hp
    obtain ⟨anti,⟨a,ha,i,hi,rfl⟩,⟨b,hb,j,hj,rfl⟩⟩ := Finset.mem_filter.mp hp
    have total : a+i+(b+j)=s := Finset.HasAntidiagonal.mem_antidiagonal.mp anti
    refine mem_biUnion.mpr ⟨(i,j), mem_product.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le hi),mem_range.mpr (Nat.lt_succ_of_le hj)⟩,?_⟩
    exact mem_image.mpr ⟨(a,b),mem_filter.mpr
      ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by dsimp; omega),ha,hb⟩,rfl⟩
  calc
    _ ≤ (offsets.biUnion shifted).card := Finset.card_le_card sub
    _ ≤ ∑ u ∈ offsets, (shifted u).card := card_biUnion_le
    _ ≤ ∑ _u ∈ offsets, K := by
      apply sum_le_sum
      intro u _
      calc _ ≤ (P (s-(u.1+u.2))).card := card_image_le
           _ = sumRep B (s-(u.1+u.2)) := by simp only [P,sumRep_def]
           _ ≤ _ := cap _
    _ = _ := by simp [offsets,pow_two]

/-- Bounded backward gaps in kB can be filled without increasing the
number of summands. Each summand may move by an offset from a fixed interval. -/
theorem fill_gaps {B : Set ℕ} {k d : ℕ} (hk : 0<k)
    (gaps : ∀ n : ℕ, ∃ m ≤ n, m ∈ k • B ∧ n ≤ m+d) :
    (B+Set.Iic d).IsAddBasisOfOrder k := by
  intro n
  obtain ⟨m,mn,hm,near⟩ := gaps n
  rw [nsmul_add]
  refine ⟨m,hm,n-m,?_,by change m+(n-m)=n; omega⟩
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [succ_nsmul]
  exact ⟨0,zero_in_sums (D:=Set.Iic d) (Nat.zero_le _) j,n-m,by
    change n-m ≤ d
    omega,by simp⟩

/-- The base case tests only bases of order three at the critical density. -/
def H1 : Prop :=
  ∀ A : Set ℕ, 0 ∈ A → 1 ∈ A → A.IsAddBasisOfOrder 3 →
    (fun n : ℕ ↦ Real.sqrt (n:ℝ)) =O[atTop] (fun n ↦ ((A ∩ Set.Icc 1 n).ncard : ℝ)) →
    ∀ K : ℕ, ∃ n : ℕ, K < sumRep A n

/-- From a possible example of order j+4, ask only for a capped set whose
(j+3)-fold sumset has bounded gaps. The new set may depend on the example. -/
def H2 : Prop :=
  ∀ (j : ℕ) (A : Set ℕ), 0 ∈ A → 1 ∈ A → A.IsAddBasisOfOrder (j+4) →
    (fun n : ℕ ↦ Real.sqrt (n:ℝ)) =O[atTop] (fun n ↦ ((A ∩ Set.Icc 1 n).ncard : ℝ)) →
    (∃ K : ℕ, ∀ n, sumRep A n ≤ K) →
    ∃ (B : Set ℕ) (L d : ℕ), 0 ∈ B ∧ (∀ n, sumRep B n ≤ L) ∧
      ((fun n : ℕ ↦ Real.sqrt (n:ℝ)) =O[atTop] (fun n ↦ ((B ∩ Set.Icc 1 n).ncard : ℝ))) ∧
      ∀ n : ℕ, ∃ m ≤ n, m ∈ (j+3) • B ∧ n ≤ m+d

theorem main : H1 → H2 → type_of% @Erdos40.erdos_40.variants.weaker := by
  classical
  intro base step
  have noCap (j : ℕ) (A : Set ℕ) (zeroA : 0 ∈ A) (oneA : 1 ∈ A)
      (order : A.IsAddBasisOfOrder (j+3))
      (dense : (fun n : ℕ ↦ Real.sqrt (n:ℝ)) =O[atTop]
        (fun n ↦ ((A ∩ Set.Icc 1 n).ncard : ℝ))) (K : ℕ) (cap : ∀ n, sumRep A n ≤ K) :
      False := by
    induction j generalizing A K with
    | zero =>
      obtain ⟨n,high⟩ := base A zeroA oneA (by simpa using order) dense K
      exact high.not_ge (cap n)
    | succ j ih =>
      obtain ⟨B,L,d,b0,bCap,bDense,gaps⟩ := step j A zeroA oneA
        (by simpa only [Nat.succ_add] using order) dense ⟨K,cap⟩
      let C := B+Set.Iic (d+1)
      have sub : B ⊆ C := fun b hb ↦ ⟨b,hb,0,Nat.zero_le _,Nat.add_zero _⟩
      have c1 : 1 ∈ C := ⟨0,b0,1,by exact Nat.succ_le_succ (Nat.zero_le _),rfl⟩
      have cOrder : C.IsAddBasisOfOrder (j+3) :=
        fill_gaps (by omega) (fun n ↦ by
          obtain ⟨m,mn,hm,near⟩ := gaps n
          exact ⟨m,mn,hm,by omega⟩)
      have sizes : (fun n : ℕ ↦ ((B ∩ Set.Icc 1 n).ncard : ℝ)) =O[atTop]
          (fun n ↦ ((C ∩ Set.Icc 1 n).ncard : ℝ)) := by
        apply Asymptotics.IsBigO.of_bound 1
        apply Eventually.of_forall
        intro n
        simp only [Real.norm_natCast,one_mul,← entries_card]
        exact_mod_cast Finset.card_le_card (entries_mono sub n)
      exact ih C (sub b0) c1 cOrder (bDense.trans sizes) _ (thickening_cap B bCap (d+1))
  apply exists_denominator_iff_finite_bases.mpr
  rintro A zeroA oneA ⟨j,order⟩ dense
  by_contra failed
  obtain ⟨K,cap⟩ := global_cap_of_limsup_ne_top A failed
  have padded : A.IsAddBasisOfOrder (j+3) := by
    intro n
    rw [add_nsmul]
    exact ⟨n,order n,0,zero_in_sums zeroA 3,Nat.add_zero _⟩
  exact noCap j A zeroA oneA padded dense K cap

end OMA.R_Erdos40_erdos_40_variants_weaker_R3
