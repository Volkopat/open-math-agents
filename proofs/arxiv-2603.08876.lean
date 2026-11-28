import OMAStatements.S_arxiv_2603_08876


/-!
# An isolated cut attains the global maximum

This proves Conjecture 5.1 of Nevena Marić, *Hierarchical threshold structure in
Max-Cut with geometric edge weights* (arXiv:2603.08876), against the statement
contributed by pyaf. Her Theorem 4.10 supplies the winning isolated cut on each
of its threshold intervals.

We write a cut as a Boolean word, and retain the cut height and a geometric
mass. Prepending a bit transforms every affine score into a positive multiple
of a child score plus a constant. For q at least 4/5 we propagate all scores
through prefixes and their reflections, using explicit chord bounds. Orders 7
through 11 use rational interval certificates checked by kernel reduction. For
q at most 4/5, a direct tail estimate proves optimality of the first singleton.
The mathematical proof and original verifier are available in desk note 82622.
-/


namespace GeometricMaxCut

open Finset OMA.S_arxiv_2603_08876

theorem laterEdges_formula {n : ℕ} (i j : Fin n) (hij : i < j) :
    laterEdges n (i,j) = (n - 1 - i.val).choose 2 + (n - 1 - j.val) := by
  classical
  let T := ↥(Ioi i)
  let liftEdge : T × T → Fin n × Fin n := fun p => (p.1.val, p.2.val)
  let tail := (univ.filter (fun p : T × T => p.1 < p.2)).image liftEdge
  let row := (Ioi j).image (fun k => (i,k))
  have ht (e : Fin n × Fin n) : e ∈ tail ↔ i < e.1 ∧ e.1 < e.2 := by
    constructor
    · intro he
      obtain ⟨⟨a,b⟩, hab, heq⟩ := mem_image.mp he
      subst e
      exact ⟨mem_Ioi.mp a.property, (mem_filter.mp hab).2⟩
    · rintro ⟨hai,hab⟩
      refine mem_image.mpr ⟨(⟨e.1, mem_Ioi.mpr hai⟩, ⟨e.2, mem_Ioi.mpr (lt_trans hai hab)⟩), ?_, ?_⟩
      · exact mem_filter.mpr ⟨mem_univ _, hab⟩
      · rfl
  have hr (e : Fin n × Fin n) : e ∈ row ↔ i = e.1 ∧ j < e.2 := by
    constructor
    · intro he
      obtain ⟨k,hk,rfl⟩ := mem_image.mp he
      exact ⟨rfl,mem_Ioi.mp hk⟩
    · rintro ⟨hi,hj⟩
      exact mem_image.mpr ⟨e.2,mem_Ioi.mpr hj,Prod.ext hi rfl⟩
  have heq : ((edges n).filter fun f => i < f.1 ∨ (i = f.1 ∧ j < f.2)) = tail ∪ row := by
    ext e
    simp only [mem_filter,edges,mem_univ,true_and,mem_union, ht,hr]
    grind
  have hd : Disjoint tail row := by
    apply disjoint_left.mpr
    intro e he hre
    exact (ne_of_lt ((ht e).mp he).1) ((hr e).mp hre).1
  have hT : Fintype.card T = n - 1 - i.val := by
    change Fintype.card ↥(Ioi i) = _
    rw [Fintype.card_coe,Fin.card_Ioi]
  have hl : Function.Injective liftEdge := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  unfold laterEdges
  rw [heq,card_union_of_disjoint hd]
  change ((univ.filter _).image liftEdge).card + ((Ioi j).image _).card = _
  rw [card_image_of_injective _ hl,
    card_image_of_injective _ (fun a b h => congrArg Prod.snd h),
    Fintype.card_product_filter_lt,hT,Fin.card_Ioi]

end GeometricMaxCut

namespace GeometricMaxCut

noncomputable def geomMass (q : ℝ) : List Bool → ℝ
  | [] => 0
  | b :: w => (if b then 1 else 0) + q * geomMass q w

noncomputable def geomTotal (q : ℝ) (n : ℕ) : ℝ := geomMass q (List.replicate n true)

noncomputable def geomCut (q : ℝ) : List Bool → ℝ
  | [] => 0
  | b :: w => (if b then geomTotal q w.length - geomMass q w else geomMass q w) +
      q ^ w.length * geomCut q w

def prefixWord (n h : ℕ) (rev : Bool) : List Bool :=
  List.replicate h (!rev) ++ List.replicate (n-h) rev

noncomputable def score (q t : ℝ) (w : List Bool) : ℝ := geomCut q w + t * geomMass q w

def Eligible (q : ℝ) (n k : ℕ) : Prop :=
  k ≤ n/2 ∧ ∀ j ≤ k, geomCut q (prefixWord n j false) ≤ geomCut q (prefixWord n k false)

def HullAt (q : ℝ) (n : ℕ) : Prop :=
  ∀ (w : List Bool), w.length = n → ∀ t : ℝ,
  ∃ k rev, Eligible q n k ∧ score q t w ≤ score q t (prefixWord n k rev)

theorem prefixWord_length {n h : ℕ} (hh : h ≤ n) (rev : Bool) :
    (prefixWord n h rev).length = n := by simp [prefixWord]; omega

theorem geomTotal_succ (q : ℝ) (n : ℕ) :
    geomTotal q (n+1) = 1 + q * geomTotal q n := by
  simp [geomTotal,List.replicate_succ,geomMass]

theorem geomMass_compl (q : ℝ) (w : List Bool) :
    geomMass q (w.map Bool.not) = geomTotal q w.length - geomMass q w := by
  induction w with
  | nil => simp [geomMass,geomTotal]
  | cons b w ih =>
    cases b <;> simp [geomMass,geomTotal_succ,ih] <;> ring

theorem geomCut_compl (q : ℝ) (w : List Bool) :
    geomCut q (w.map Bool.not) = geomCut q w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [geomCut,geomMass_compl,ih]

theorem prefixWord_compl (n k : ℕ) :
    (prefixWord n k false).map Bool.not = prefixWord n k true := by
  simp [prefixWord,List.map_replicate]

theorem geomCut_prefix_compl (q : ℝ) (n k : ℕ) :
    geomCut q (prefixWord n k true) = geomCut q (prefixWord n k false) := by
  rw [← prefixWord_compl,geomCut_compl]

theorem cons_preserves_scores {q t : ℝ} (hq : 0 < q) (b : Bool) {v w : List Bool}
    (len : v.length = w.length)
    (h : score q ((t*q + (if b then -1 else 1)) / q^v.length) v ≤
         score q ((t*q + (if b then -1 else 1)) / q^v.length) w) :
    score q t (b::v) ≤ score q t (b::w) := by
  have hp : 0 < q^v.length := pow_pos hq _
  have H := (mul_le_mul_of_nonneg_left h hp.le)
  unfold score at *
  simp only [geomCut, geomMass, ←len]
  field_simp [ne_of_gt hp] at H
  cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> nlinarith

theorem hull_succ {q : ℝ} (hq : 0 < q) {n : ℕ} (ih : HullAt q n)
    (step : ∀ b k rev, Eligible q n k → ∀ t : ℝ,
      ∃ j s, Eligible q (n+1) j ∧
        score q t (b :: prefixWord n k rev) ≤ score q t (prefixWord (n+1) j s)) :
    HullAt q (n+1) := by
  intro l hl t
  cases l with
  | nil => simp at hl
  | cons b w =>
    have hw : w.length = n := by simpa using hl
    obtain ⟨k,rev,hk,h⟩ := ih w hw ((t*q + (if b then -1 else 1))/q^w.length)
    have len : w.length = (prefixWord n k rev).length :=
      hw.trans (prefixWord_length (by have := hk.1; omega) rev).symm
    obtain ⟨j,s,hj,hstep⟩ := step b k rev hk t
    exact ⟨j,s,hj,(cons_preserves_scores hq b len h).trans hstep⟩

end GeometricMaxCut

namespace GeometricMaxCut

open Finset OMA.S_arxiv_2603_08876

def edgeIndex : ℕ → ℕ → ℕ → ℕ
  | n+1, i+1, j+1 => n + edgeIndex n i j
  | _, 0, j+1 => j
  | _, _, _ => 0

theorem edgeIndex_add_after {n i j : ℕ} (hij : i < j) (hjn : j < n) :
    edgeIndex n i j + ((n-1-i).choose 2 + (n-1-j)) = n.choose 2 - 1 := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      cases i with
      | zero =>
        simp [edgeIndex]
        omega
      | succ i =>
        have H := ih (i:=i) (j:=j) (by omega) (by omega)
        have h2 : 0 < n.choose 2 := Nat.choose_pos (by omega)
        simp only [edgeIndex]
        have h₁ : n+1-1-(i+1) = n-1-i := by omega
        have h₂ : n+1-1-(j+1) = n-1-j := by omega
        rw [h₁,h₂]
        change n + edgeIndex n i j + ((n-1-i).choose 2 + (n-1-j)) = n + n.choose 2 - 1
        omega

theorem geomMass_ofFn (q : ℝ) {n : ℕ} (f : Fin n → Bool) :
    geomMass q (List.ofFn f) = ∑ i, if f i then q^(i.val) else 0 := by
  induction n with
  | zero => simp [geomMass]
  | succ n ih =>
    rw [List.ofFn_succ, geomMass, ih, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases f i.succ <;> simp [mul_comm]

theorem geomTotal_sum (q : ℝ) (n : ℕ) : geomTotal q n = ∑ i : Fin n, q^i.val := by
  rw [geomTotal, ←List.ofFn_const n true, geomMass_ofFn]
  simp

theorem geomCut_ofFn (q : ℝ) {n : ℕ} (f : Fin n → Bool) :
    geomCut q (List.ofFn f) = ∑ i, ∑ j,
      if i < j ∧ f i ≠ f j then q^edgeIndex n i.val j.val else 0 := by
  induction n with
  | zero => simp [geomCut]
  | succ n ih =>
    rw [List.ofFn_succ,geomCut,Fin.sum_univ_succ]
    simp_rw [Fin.sum_univ_succ (f := fun j => if _ < j ∧ _ then _ else (0 : ℝ))]
    simp only [not_lt_zero,false_and,ite_false,zero_add,Fin.succ_pos,true_and,
      Fin.succ_lt_succ_iff,Fin.val_succ,Fin.val_zero,edgeIndex,List.length_ofFn,ih]
    congr 1
    · rw [geomMass_ofFn,geomTotal_sum]
      cases hb : f 0
      · simp only [Bool.false_eq_true,if_false]
        apply Finset.sum_congr rfl
        intro j _
        cases f j.succ <;> simp
      · simp only [if_true,←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        cases f j.succ <;> simp
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp_all [pow_add]

theorem cast_source {n : ℕ} (q : ℝ) (hq : 0 < q) (S : Finset (Fin n)) :
    geomCut q (List.ofFn (fun i => decide (i ∈ S))) =
      q^(n.choose 2 - 1) * cutWeight n q⁻¹ S := by
  rw [geomCut_ofFn,cutWeight,Finset.mul_sum]
  simp only [edges,Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · have he : edgeIndex n i.val j.val + laterEdges n (i,j) = n.choose 2 - 1 := by
      rw [laterEdges_formula i j hij]
      exact edgeIndex_add_after hij j.isLt
    have eq : q^(n.choose 2-1)*(q⁻¹)^laterEdges n (i,j) = q^edgeIndex n i.val j.val := by
      rw [←he, pow_add, inv_pow]
      field_simp
    rw [inv_pow] at eq
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hij,hi,hj,eq]
  · simp [hij]

theorem prefix_source {n k : ℕ} (hk : k ≤ n) :
    List.ofFn (fun i : Fin n => decide (i ∈ isolatedCut n k)) = prefixWord n k false := by
  apply List.ext_getElem
  · simp [prefixWord_length hk]
  · intro i hi hj
    by_cases h : i < k <;>
      simp [isolatedCut,prefixWord,List.getElem_append,h]

theorem conclusion_of_hull {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) (H : HullAt q n) :
    ∃ k, 1 ≤ k ∧ k ≤ n/2 ∧ ∀ S : Finset (Fin n),
      cutWeight n q⁻¹ S ≤ cutWeight n q⁻¹ (isolatedCut n k) := by
  classical
  let ks := Icc 1 (n/2)
  have hne : ks.Nonempty := ⟨1,mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
  obtain ⟨best,hbest,maximal⟩ := exists_max_image ks (fun k => cutWeight n q⁻¹ (isolatedCut n k)) hne
  obtain ⟨hb₁,hb₂⟩ := mem_Icc.mp hbest
  refine ⟨best,hb₁,hb₂,?_⟩
  intro S
  let w := List.ofFn (fun i : Fin n => decide (i ∈ S))
  have lw : w.length = n := by simp [w]
  obtain ⟨k,rev,hk,hs⟩ := H w lw 0
  have hcut : geomCut q w ≤ geomCut q (prefixWord n k false) := by
    cases rev <;> simpa [score,geomCut_prefix_compl] using hs
  have hkn : k ≤ n := by have := hk.1; omega
  rw [←prefix_source hkn,cast_source q hq (isolatedCut n k)] at hcut
  change geomCut q (List.ofFn fun i => decide (i ∈ S)) ≤ _ at hcut
  rw [cast_source q hq S] at hcut
  have hr := le_of_mul_le_mul_left hcut (pow_pos hq _)
  by_cases z : k = 0
  · subst k
    have hempty : isolatedCut n 0 = ∅ := by simp [isolatedCut]
    have h0 : cutWeight n q⁻¹ (∅ : Finset (Fin n)) = 0 := by simp [cutWeight]
    rw [hempty,h0] at hr
    exact hr.trans (Finset.sum_nonneg (fun _ _ => pow_nonneg (inv_nonneg.mpr hq.le) _))
  · exact hr.trans (maximal k (mem_Icc.mpr ⟨by omega,hk.1⟩))

end GeometricMaxCut

namespace GeometricMaxCut

open Finset

/-- Mass of a consecutive block of vertices with column weights q^j. -/
noncomputable def rowMass (q : ℝ) (start len : ℕ) : ℝ :=
  ∑ i ∈ range len, q ^ (start + i)

theorem rowMass_mono_length {q : ℝ} (hq : 0 ≤ q) (start : ℕ) {k l : ℕ}
    (hkl : k ≤ l) : rowMass q start k ≤ rowMass q start l := by
  exact sum_le_sum_of_subset_of_nonneg (range_mono hkl)
    (fun i _ _ => pow_nonneg hq _)

private theorem chord_separation {q : ℝ} {h L : ℕ}
    (hq : 4 / 5 ≤ q) (hq1 : q ≤ 1) (hh : 2 ≤ h)
    (hhL : h ≤ L) (hm : 12 ≤ h + L + 1)
    (hpower : 2 / 3 ≤ q ^ (h - 1))
    (hchild : rowMass q 1 (h-1) ≤ rowMass q (h+1) L) :
    1 - q^h ≤ rowMass q (h+1) L * (1 - q^(L-1)) := by
  have hq0 : 0 ≤ q := by linarith
  have hq0' : 0 ≤ 1 - q^(L-1) := sub_nonneg.mpr (pow_le_one₀ hq0 hq1)
  by_cases hs : h ≤ 3
  · have hl : h ≤ L - 1 := by omega
    have hu : 1 ≤ rowMass q (h+1) L := by
      interval_cases h
      · calc
          1 ≤ (4/5:ℝ)^3 + (4/5:ℝ)^4 + (4/5:ℝ)^5 := by norm_num
          _ ≤ q^3 + q^4 + q^5 := by gcongr
          _ = rowMass q 3 3 := by simp [rowMass, sum_range_succ]
          _ ≤ rowMass q 3 L := rowMass_mono_length hq0 3 (by omega)
      · calc
          1 ≤ (4/5:ℝ) + (4/5:ℝ)^2 := by norm_num
          _ ≤ q + q^2 := by gcongr
          _ = rowMass q 1 (3-1) := by simp [rowMass, sum_range_succ]
          _ ≤ _ := hchild
    calc
      1 - q^h ≤ 1 - q^(L-1) := sub_le_sub_left (pow_le_pow_of_le_one hq0 hq1 hl) 1
      _ ≤ _ := le_mul_of_one_le_left hq0' hu
  · have h4 : 4 ≤ h := by omega
    have small (j : ℕ) (hj : j ≤ h-1) : (2/3 : ℝ) ≤ q^j :=
      hpower.trans (pow_le_pow_of_le_one hq0 hq1 hj)
    have hu : 2 ≤ rowMass q (h+1) L := by
      calc
        2 ≤ q^1 + q^2 + q^3 := by linarith [small 1 (by omega), small 2 (by omega),
                                             small 3 (by omega)]
        _ = rowMass q 1 3 := by simp [rowMass, sum_range_succ]
        _ ≤ rowMass q 1 (h-1) := rowMass_mono_length hq0 1 (by omega)
        _ ≤ _ := hchild
    have hp : q^(h-1) ≤ q := by simpa using
      (pow_le_pow_of_le_one hq0 hq1 (show 1 ≤ h-1 by omega))
    have hp1 : q^(h-1) ≤ 1 := pow_le_one₀ hq0 hq1
    have hsuc : h-1+1 = h := by omega
    have hdecomp : q^h = q^(h-1) * q := by rw [← pow_succ, hsuc]
    have hhalf : 1-q^h ≤ 2 * (1-q^(h-1)) := by
      rw [hdecomp]
      nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1)]
    calc
      _ ≤ 2 * (1-q^(h-1)) := hhalf
      _ ≤ 2 * (1-q^(L-1)) := mul_le_mul_of_nonneg_left
        (sub_le_sub_left (pow_le_pow_of_le_one hq0 hq1 (by omega : h-1 ≤ L-1)) 1) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right hu hq0'

/-- Nonnegativity of the one-hole chord deficit in the all-orders induction.
The two child hypotheses are the geometric consequences of prefix eligibility.
The formula is the cut-weight difference in equation (3) of the manuscript. -/
theorem blockChord_nonneg {q R : ℝ} {h L : ℕ} (ρ : ℕ → ℝ)
    (hq : 4 / 5 ≤ q) (hq1 : q ≤ 1) (hh : 2 ≤ h)
    (hhL : h ≤ L) (hm : 12 ≤ h + L + 1)
    (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hρ : ∀ i ∈ range (h-2), R ≤ ρ (i+1))
    (hpower : 2 / 3 ≤ q ^ (h-1))
    (hchild : rowMass q 1 (h-1) ≤ rowMass q (h+1) L) :
    0 ≤ rowMass q (h+1) L * (1-R + R*q^h*(1-q^(L-1)))
      - (∑ i ∈ range (h-2), q^(1+i) * (1-ρ (i+1)))
      - (q^(h-1)+q^h-1) * (1-R*q^h) := by
  have hq0 : 0 ≤ q := by linarith
  have hz : 0 ≤ q^h := pow_nonneg hq0 _
  have hz1 : q^h ≤ 1 := pow_le_one₀ hq0 hq1
  have hv1 : q^(h-1) ≤ 1 := pow_le_one₀ hq0 hq1
  have sep := chord_separation hq hq1 hh hhL hm hpower hchild
  have hu : rowMass q 1 (h-2) + q^(h-1) ≤ rowMass q (h+1) L := by
    convert hchild using 1
    unfold rowMass
    have hl : h-1 = h-2+1 := by omega
    rw [hl, sum_range_succ]
    congr 2
    omega
  have hcost : (∑ i ∈ range (h-2), q^(1+i) * (1-ρ (i+1)))
      ≤ rowMass q 1 (h-2) * (1-R) := by
    unfold rowMass
    rw [sum_mul]
    exact sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (sub_le_sub_left (hρ i hi) 1) (pow_nonneg hq0 _)
  nlinarith only [hcost,
    mul_nonneg (sub_nonneg.mpr hR1) (sub_nonneg.mpr hu),
    mul_nonneg (sub_nonneg.mpr hR1) (sub_nonneg.mpr hz1),
    mul_nonneg hR (mul_nonneg hz (sub_nonneg.mpr sep)),
    mul_nonneg hR (mul_nonneg (sub_nonneg.mpr hv1) (sub_nonneg.mpr hz1))]

theorem geometric_decay (L : ℕ) (hL : 2 ≤ L) :
    (L : ℝ) * (2/3:ℝ)^L ≤ 1 := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [Nat.cast_succ, pow_succ]
    have hl : (2:ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ (2/3:ℝ)^L by positivity)]

/-- Multiply the actual adjacent row ratios before the last included child row. -/
theorem row_decay_of_step {q : ℝ} {h L : ℕ} (ρ : ℕ → ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hn : ∀ i < h-1, 0 ≤ ρ i)
    (hstep : ∀ i < h-1, ρ (i+1) = ρ i * q^(h+L-i-2)) :
    ∀ i ∈ range (h-1), ρ (h-1) ≤ ρ i * q^((h-1-i)*L) := by
  have walk (d i : ℕ) (he : i+d ≤ h-1) :
      ρ (i+d) ≤ ρ i * q^(d*L) := by
    induction d with
    | zero => simp
    | succ d ih =>
      have hlt : i+d < h-1 := by omega
      have hed : L ≤ h+L-(i+d)-2 := by omega
      calc
        ρ (i+(d+1)) = ρ (i+d) * q^(h+L-(i+d)-2) := hstep (i+d) hlt
        _ ≤ ρ (i+d) * q^L :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq hq1 hed) (hn _ hlt)
        _ ≤ (ρ i * q^(d*L)) * q^L :=
          mul_le_mul_of_nonneg_right (ih (by omega)) (pow_nonneg hq _)
        _ = _ := by rw [Nat.succ_mul, pow_add, mul_assoc]
  intro i hi
  have hii := mem_range.mp hi
  have hwalk := walk (h-1-i) i (by omega)
  simpa only [show i+(h-1-i) = h-1 by omega] using hwalk

/-- Equation (3) directly from weighted prefix eligibility and the quantitative
decay of the child row factors. The decay follows by multiplying the adjacent
row ratios, each at most q^L before index h-1. -/
theorem eligibleBlockChord {q R : ℝ} {h L : ℕ} (ρ : ℕ → ℝ)
    (hq : 4 / 5 ≤ q) (hq1 : q ≤ 1) (hh : 2 ≤ h) (hhL : h ≤ L)
    (hm : 12 ≤ h + L + 1) (hR : 0 < R) (hinit : ρ 0 = 1)
    (hn : ∀ i ∈ range (h-1), 0 ≤ ρ i)
    (hrows : ∀ i ∈ range (h-1), R ≤ ρ i * q^((h-1-i)*L))
    (heligible : ∑ i ∈ range (h-1), ρ i ≤ R * rowMass q 1 L) :
    0 ≤ rowMass q (h+1) L * (1-R + R*q^h*(1-q^(L-1)))
      - (∑ i ∈ range (h-2), q^(1+i) * (1-ρ (i+1)))
      - (q^(h-1)+q^h-1) * (1-R*q^h) := by
  have hq0 : 0 ≤ q := by linarith
  have h0 : 0 ∈ range (h-1) := mem_range.mpr (by omega)
  have hdec : R ≤ (q^(h-1))^L := by
    simpa [hinit,pow_mul] using hrows 0 h0
  have hlen : rowMass q 1 L ≤ L := by
    calc
      _ ≤ ∑ _i ∈ range L, (1:ℝ) := sum_le_sum fun i _ => pow_le_one₀ hq0 hq1
      _ = _ := by simp
  have hone : (1:ℝ) ≤ R*L := by
    calc
      1 = ρ 0 := hinit.symm
      _ ≤ _ := single_le_sum hn h0
      _ ≤ _ := heligible
      _ ≤ _ := mul_le_mul_of_nonneg_left hlen hR.le
  have hpow : (2/3:ℝ) ≤ q^(h-1) := by
    by_contra! hbad
    have hL0 : 0 < (L:ℝ) := by exact_mod_cast (show 0 < L by omega)
    have hlt := mul_lt_mul_of_pos_left
      (pow_lt_pow_left₀ hbad (pow_nonneg hq0 _) (by omega : L ≠ 0)) hL0
    nlinarith [geometric_decay L (by omega), mul_nonneg hL0.le (sub_nonneg.mpr hdec)]
  have hu : rowMass q (h+1) L = q^h * rowMass q 1 L := by
    unfold rowMass
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [← pow_add]
    congr 1
    omega
  apply blockChord_nonneg ρ hq hq1 hh hhL hm hR.le
  · exact hdec.trans (pow_le_one₀ (pow_nonneg hq0 _) (pow_le_one₀ hq0 hq1))
  · intro i hi
    have hi' : i+1 ∈ range (h-1) := mem_range.mpr (by have := mem_range.mp hi; omega)
    exact (hrows _ hi').trans (mul_le_of_le_one_right (hn _ hi') (pow_le_one₀ hq0 hq1))
  · exact hpow
  · apply le_of_mul_le_mul_left (a := R) _ hR
    rw [hu]
    calc
      R * rowMass q 1 (h-1) = ∑ i ∈ range (h-1), R*q^(1+i) := by
        simp only [rowMass, mul_sum]
      _ ≤ ∑ i ∈ range (h-1), q^h * ρ i := by
        apply sum_le_sum
        intro i hi
        have hi' := mem_range.mp hi
        have hrel : h-1-i ≤ (h-1-i)*L := by
          simpa using Nat.mul_le_mul_left (h-1-i) (show 1 ≤ L by omega)
        have hp := pow_le_pow_of_le_one hq0 hq1 hrel
        have hr := (hrows i hi).trans (mul_le_mul_of_nonneg_left hp (hn i hi))
        have hprod := mul_le_mul_of_nonneg_right hr (pow_nonneg hq0 (1+i))
        convert hprod using 1
        rw [mul_assoc, ← pow_add, show h-1-i+(1+i) = h by omega, mul_comm]
      _ = q^h * ∑ i ∈ range (h-1), ρ i := (mul_sum _ _ _).symm
      _ ≤ q^h * (R * rowMass q 1 L) := mul_le_mul_of_nonneg_left heligible (pow_nonneg hq0 _)
      _ = _ := by ring


end GeometricMaxCut

namespace GeometricMaxCut

open Finset

theorem rowMass_mono_base {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (s n : ℕ) :
    rowMass q s n ≤ rowMass r s n :=
  sum_le_sum fun _ _ => pow_le_pow_left₀ hq hqr _

theorem rowMass_add (q : ℝ) (s a b : ℕ) :
    rowMass q s (a+b) = rowMass q s a + rowMass q (s+a) b := by
  simp only [rowMass, sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Nat.add_assoc]

theorem rowMass_shift (q : ℝ) (s a b : ℕ) :
    rowMass q (s+a) b = q^s * rowMass q a b := by
  unfold rowMass
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← pow_add, Nat.add_assoc]

theorem rowMass_le_length {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (s n : ℕ) :
    rowMass q s n ≤ n := by
  calc
    _ ≤ ∑ _i ∈ range n, (1:ℝ) := sum_le_sum fun i _ => pow_le_one₀ hq hq1
    _ = _ := by simp

private theorem overlap {h L : ℕ} (h3 : 3 ≤ h) (hl : h < L) (hm : 12 ≤ h+L+1) :
    (h:ℝ)*(h+1)+(L-h)*(h+L) ≤
      (L-h)*((L-1)*h*(h-1)/2-(h-1)) := by
  by_cases h5 : 5 ≤ h
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h5
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show (5+a)+1 ≤ L by omega)
    apply sub_nonneg.mp
    push_cast
    ring_nf
    positivity
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show 6 ≤ L by omega)
    interval_cases h <;> apply sub_nonneg.mp <;> push_cast <;> ring_nf <;> positivity

private theorem small_parameter {q : ℝ} {h L : ℕ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hl : h ≤ L)
    (hx : (1-q)*((h:ℝ)*(h+1)+(L-h)*(h+L)) ≤ L-h) :
    rowMass q 0 h ≤ rowMass q (h+1) L := by
  have hp := one_add_mul_sub_le_pow (show -1 ≤ q by linarith) (h+1)
  push_cast at hp
  have hb := rowMass_le_length hq hq1 0 h
  have hp1 := pow_le_one₀ hq hq1 (n := h+1)
  have hfirst : rowMass q 0 h - (h:ℝ)*(h+1)*(1-q) ≤ rowMass q (h+1) h := by
    rw [show h+1 = (h+1)+0 by omega, rowMass_shift]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hp1),
      mul_nonneg (show 0 ≤ (h:ℝ) by positivity) (sub_nonneg.mpr hp)]
  have ht : (L-h:ℝ)*(1-(h+L)*(1-q)) ≤ rowMass q (h+1+h) (L-h) := by
    calc
      _ = ∑ _i ∈ range (L-h), (1-(h+L:ℝ)*(1-q)) := by
        simp [Nat.cast_sub hl]
        ring
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        have hi' := mem_range.mp hi
        have hi'' : h+1+h+i ≤ h+L := by omega
        have hpower := pow_le_pow_of_le_one hq hq1 hi''
        have hber := one_add_mul_sub_le_pow (show -1 ≤ q by linarith) (h+L)
        push_cast at hber
        linarith
  have split := rowMass_add q (h+1) h (L-h)
  rw [show h+(L-h) = L by omega] at split
  rw [split]
  linarith

theorem sum_succ_cast (n : ℕ) :
    ∑ i ∈ range n, ((i:ℝ)+1) = (n:ℝ)*(n+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

private theorem inverse_gap {q : ℝ} {k d : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 1 ≤ k) :
    (1/q)^k + (1/q) * d * (1-q) ≤ (1/q)^(k+d) := by
  let u := 1/q
  change u^k + u * d * (1-q) ≤ u^(k+d)
  have hu : 1 ≤ u := (le_div_iff₀ hq).mpr (by simpa using hq1)
  have ht : 1-q ≤ u-1 := by
    have ht' : 2-q ≤ 1/q := (le_div_iff₀ hq).mpr (by nlinarith [sq_nonneg (1-q)])
    dsimp [u]; linarith
  have hum : u ≤ u^k := by simpa using pow_le_pow_right₀ hu hk
  have hp := one_add_mul_sub_le_pow (show -1 ≤ u by linarith) d
  rw [pow_add]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hum)
      (mul_nonneg (show 0 ≤ (d:ℝ) by positivity) (sub_nonneg.mpr hq1)),
    mul_nonneg (show 0 ≤ u^k by positivity)
      (mul_nonneg (show 0 ≤ (d:ℝ) by positivity) (sub_nonneg.mpr ht)),
    mul_nonneg (show 0 ≤ u^k by positivity) (sub_nonneg.mpr hp)]

/-- Reversing the powers in a prefix sum. -/
theorem rowMass_inverse (q : ℝ) (hq : 0 < q) (h : ℕ) :
    rowMass q 0 h = q^h * rowMass (1/q) 1 h := by
  unfold rowMass
  rw [mul_sum]
  simp only [zero_add]
  rw [← sum_range_reflect (fun i => q^i) h]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [one_div, inv_pow, ← div_eq_mul_inv]
  apply (eq_div_iff (pow_ne_zero _ hq.ne')).mpr
  rw [← pow_add, show h-1-i+(1+i) = h by omega]

private theorem large_parameter {q : ℝ} {h L : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 3 ≤ h) (hl : h ≤ L)
    (hel : ∑ i ∈ range (h-1), (1/q)^((i+1)*L) ≤ rowMass q 1 L)
    (hx : 1 ≤ (1-q)*(((L:ℝ)-1)*h*(h-1)/2-(h-1))) :
    rowMass q 0 h ≤ rowMass q (h+1) L := by
  let u := 1/q
  have hsum : ∑ i ∈ range (h-1), (u^(2+i) + (u*(1-q))*((L-1:ℝ)*(i+1)-1))
      ≤ ∑ i ∈ range (h-1), u^((i+1)*L) := by
    apply sum_le_sum
    intro i _
    have hd : 2+i ≤ (i+1)*L := by
      have := Nat.mul_le_mul_left (i+1) (show 2 ≤ L by omega)
      omega
    have term := inverse_gap (k := 2+i) (d := (i+1)*L-(2+i)) hq hq1 (by omega)
    rw [show 2+i+((i+1)*L-(2+i)) = (i+1)*L by omega, Nat.cast_sub hd] at term
    push_cast at term
    dsimp [u]
    nlinarith only [term]
  have coeff : ∑ i ∈ range (h-1), ((L-1:ℝ)*(i+1)-1) =
      (L-1:ℝ)*h*(h-1)/2-(h-1) := by
    rw [sum_sub_distrib, ← mul_sum, sum_succ_cast]
    simp [Nat.cast_sub (show 1 ≤ h by omega)]
    ring
  rw [sum_add_distrib, ← mul_sum, coeff] at hsum
  have he : rowMass u 1 h = u + ∑ i ∈ range (h-1), u^(2+i) := by
    have hpart := rowMass_add u 1 1 (h-1)
    rw [show 1+(h-1) = h by omega] at hpart
    simpa [rowMass] using hpart
  rw [rowMass_inverse q hq h, show h+1 = h+1 by rfl, rowMass_shift q h 1 L]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq.le _)
  change rowMass u 1 h ≤ _
  rw [he]
  have hu : 0 ≤ u := by dsimp [u]; positivity
  change ∑ i ∈ range (h-1), u^((i+1)*L) ≤ _ at hel
  nlinarith only [mul_nonneg hu (sub_nonneg.mpr hx), hsum, hel]

/-- Reverse the weighted child eligibility inequality and cancel its last
row factor. This supplies the geometric sum used in both pruning cases. -/
theorem inverse_eligibility {q R : ℝ} {h L : ℕ} (ρ : ℕ → ℝ)
    (hq : 0 < q) (hR : 0 < R)
    (hrows : ∀ i ∈ range (h-1), R ≤ ρ i * q^((h-1-i)*L))
    (hel : ∑ i ∈ range (h-1), ρ i ≤ R * rowMass q 1 L) :
    ∑ i ∈ range (h-1), (1/q)^((i+1)*L) ≤ rowMass q 1 L := by
  apply le_of_mul_le_mul_left (a := R) _ hR
  rw [← sum_range_reflect (fun i => (1/q)^((i+1)*L)) (h-1), mul_sum]
  apply le_trans _ hel
  apply sum_le_sum
  intro i hi
  have hi' := mem_range.mp hi
  rw [show h-1-1-i+1 = h-1-i by omega, one_div, inv_pow, ← div_eq_mul_inv]
  exact (div_le_iff₀ (pow_pos hq _)).mpr (hrows i hi)

/-- The remaining suffix has at least the mass of the prefix whenever the
eligible child prefix leaves a strictly longer tail. This is (4). -/
theorem noncentral_pruning {q : ℝ} {h L : ℕ} (hq : 4/5 ≤ q) (hq1 : q ≤ 1)
    (hh : 1 ≤ h) (hl : h < L) (hm : 12 ≤ h+L+1)
    (hel : ∑ i ∈ range (h-1), (1/q)^((i+1)*L) ≤ rowMass q 1 L) :
    rowMass q 0 h ≤ rowMass q (h+1) L := by
  have hq0 : 0 < q := by linarith
  by_cases hs : h ≤ 2
  · interval_cases h
    · calc
        _ ≤ (1:ℝ) := by simpa using rowMass_le_length hq0.le hq1 0 1
        _ ≤ rowMass (4/5) 2 2 := by norm_num [rowMass,sum_range_succ]
        _ ≤ rowMass q 2 2 := rowMass_mono_base (by norm_num) hq _ _
        _ ≤ _ := rowMass_mono_length hq0.le 2 (by omega)
    · calc
        _ ≤ (2:ℝ) := by simpa using rowMass_le_length hq0.le hq1 0 2
        _ ≤ rowMass (4/5) 3 7 := by norm_num [rowMass,sum_range_succ]
        _ ≤ rowMass q 3 7 := rowMass_mono_base (by norm_num) hq _ _
        _ ≤ _ := rowMass_mono_length hq0.le 3 (by omega)
  · have h3 : 3 ≤ h := by omega
    by_cases hx : 1 ≤ (1-q)*(((L:ℝ)-1)*h*(h-1)/2-(h-1))
    · exact large_parameter hq0 hq1 h3 hl.le hel hx
    · apply small_parameter hq0.le hq1 hl.le
      have hd : (h:ℝ) ≤ L := by exact_mod_cast hl.le
      nlinarith only [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr (overlap h3 hl hm)),
        mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr (le_of_not_ge hx))]


end GeometricMaxCut

namespace GeometricMaxCut

open Finset

/-- The exponent in the factor depending on the smaller endpoint, after
normalization by q. Dropping the first vertex reduces the order by one. -/
def rowExp : ℕ → ℕ → ℕ
  | n+1, i+1 => n-1 + rowExp n i
  | _, _ => 0

noncomputable def rowFactor (q : ℝ) (n i : ℕ) : ℝ := q^(rowExp n i)

noncomputable def rowSum (q : ℝ) (n h : ℕ) : ℝ :=
  ∑ i ∈ range h, rowFactor q n i

theorem rowExp_step {n i : ℕ} (hi : i < n) :
    rowExp n (i+1) = rowExp n i + (n-i-2) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [rowExp]
    | succ i =>
      simp only [rowExp]
      have H := ih (i := i) (by omega)
      omega

theorem rowFactor_step {n i : ℕ} (q : ℝ) (hi : i < n) :
    rowFactor q n (i+1) = rowFactor q n i * q^(n-i-2) := by
  simp [rowFactor, rowExp_step hi, pow_add]

theorem rowExp_parent {n i : ℕ} (hi : i < n) :
    rowExp (n+1) i = rowExp n i + i := by
  induction i with
  | zero => simp [rowExp]
  | succ i ih =>
    rw [rowExp_step (by omega : i < n+1), rowExp_step (by omega : i < n), ih (by omega)]
    omega

theorem rowFactor_parent (q : ℝ) {n i : ℕ} (hi : i < n) :
    rowFactor q (n+1) i = q^i * rowFactor q n i := by
  simp [rowFactor,rowExp_parent hi,pow_add,mul_comm]

theorem rowSum_cons (q : ℝ) (n h : ℕ) :
    rowSum q (n+1) (h+1) = 1 + q^(n-1)*rowSum q n h := by
  unfold rowSum
  rw [sum_range_succ', mul_sum]
  simp [rowFactor,rowExp,pow_add,add_comm,mul_comm]

theorem rowSum_last (q : ℝ) (n h : ℕ) :
    rowSum q n (h+1) = rowSum q n h + rowFactor q n h := by
  simp [rowSum,sum_range_succ]

theorem rowMass_cons (q : ℝ) (s n : ℕ) :
    rowMass q s (n+1) = q^s + q * rowMass q s n := by
  unfold rowMass
  rw [sum_range_succ', mul_sum, add_comm]
  simp only [Nat.add_zero]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [show s+(i+1) = (s+i)+1 by omega, pow_succ, mul_comm]

theorem geomMass_append (q : ℝ) (w v : List Bool) :
    geomMass q (w++v) = geomMass q w + q^w.length * geomMass q v := by
  induction w with
  | nil => simp [geomMass]
  | cons b w ih =>
    simp [geomMass,ih,pow_succ]
    ring

theorem geomMass_false (q : ℝ) (n : ℕ) : geomMass q (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, geomMass, ih]

theorem geomTotal_rowMass (q : ℝ) (n : ℕ) : geomTotal q n = rowMass q 0 n := by
  induction n with
  | zero => simp [geomTotal,geomMass,rowMass]
  | succ n ih => simp [geomTotal_succ,ih,rowMass_cons]

theorem prefix_mass (q : ℝ) (n h : ℕ) :
    geomMass q (prefixWord n h false) = rowMass q 0 h := by
  simp only [prefixWord, Bool.not_false, geomMass_append, geomMass_false, mul_zero, add_zero]
  exact geomTotal_rowMass q h

theorem prefix_cut (q : ℝ) {n h : ℕ} (hh : h ≤ n) :
    q * geomCut q (prefixWord n h false) = rowSum q n h * rowMass q h (n-h) := by
  induction n generalizing h with
  | zero =>
    have := hh
    obtain rfl : h = 0 := by omega
    simp [prefixWord,geomCut,rowSum]
  | succ n ih =>
    cases h with
    | zero =>
      simp only [prefixWord,List.replicate_zero,List.nil_append,Nat.sub_zero]
      have hf (k : ℕ) : geomCut q (List.replicate k false) = 0 := by
        induction k with
        | zero => rfl
        | succ k hk => simp [List.replicate_succ,geomCut,geomMass_false,hk]
      simp [hf,rowSum]
    | succ h =>
      have hh' : h ≤ n := by omega
      have hlist : prefixWord (n+1) (h+1) false = true :: prefixWord n h false := by
        simp [prefixWord,List.replicate_succ]
      rw [hlist,geomCut]
      simp only [if_true, prefixWord_length hh', prefix_mass, geomTotal_rowMass, rowSum_cons,
                 Nat.add_sub_add_right]
      have split := rowMass_add q 0 h (n-h)
      rw [show h+(n-h) = n by omega, Nat.zero_add] at split
      rw [split, show h+1 = 1+h by omega, rowMass_shift q 1 h (n-h), pow_one]
      have hn : q*q^(n-1) * rowMass q h (n-h) * rowSum q n h =
                q^n * rowSum q n h * rowMass q h (n-h) := by
        by_cases hz : n = 0
        · subst n
          obtain rfl : h = 0 := by omega
          simp [rowSum]
        · rw [show q*q^(n-1) = q^n by rw [mul_comm, ← pow_succ]; congr 1; omega]
          ring
      nlinarith only [congrArg (fun y : ℝ => q^n * y) (ih hh'), hn]

end GeometricMaxCut

namespace GeometricMaxCut

open Finset

private theorem inv_pow_bernoulli {q : ℝ} (hq : 0 < q) (d : ℕ) :
    1+(d:ℝ)*(1-q) ≤ (1/q)^d := by
  have ht : 2-q ≤ 1/q := (le_div_iff₀ hq).mpr (by nlinarith [sq_nonneg (1-q)])
  have hu : 0 ≤ 1/q := by positivity
  have hp := one_add_mul_sub_le_pow (show -1 ≤ 1/q by linarith) d
  nlinarith [mul_nonneg (show 0 ≤ (d:ℝ) by positivity) (sub_nonneg.mpr ht)]

private theorem central_parameter {q : ℝ} {h : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 6 ≤ h)
    (hel : ∑ i ∈ range (h-1), (1/q)^((i+1)*h) ≤ rowMass q 1 h) :
    (h:ℝ)^2*(h-1)/2*(1-q) ≤ 1 := by
  have lb : ∑ i ∈ range (h-1), (1 + ((h:ℝ)*(1-q))*(i+1))
      ≤ ∑ i ∈ range (h-1), (1/q)^((i+1)*h) := by
    apply sum_le_sum
    intro i _
    have hi := inv_pow_bernoulli hq ((i+1)*h)
    push_cast at hi
    linarith
  rw [sum_add_distrib, ← mul_sum, sum_succ_cast] at lb
  simp [Nat.cast_sub (show 1 ≤ h by omega)] at lb
  simp only [one_div, inv_pow] at hel
  nlinarith only [lb, hel, rowMass_le_length hq.le hq1 1 h]

private theorem central_factors {q : ℝ} {h : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 6 ≤ h) (hx : (h:ℝ)^2*(h-1)/2*(1-q) ≤ 1) :
    (h:ℝ)*(h+1)*(1-q) ≤ q^(h-1) ∧ 4 ≤ (h:ℝ)*q^(3*h-1) := by
  have hcoeff : (h:ℝ)^2+2*h-1 ≤ (h:ℝ)^2*(h-1)/2 := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hh
    apply sub_nonneg.mp; push_cast; ring_nf; positivity
  have hcoeff' : (h:ℝ)*(3*h-1) ≤ ((h:ℝ)-4)*((h:ℝ)^2*(h-1)/2) := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hh
    apply sub_nonneg.mp; push_cast; ring_nf; positivity
  have hp := one_add_mul_sub_le_pow (show -1 ≤ q by linarith) (h-1)
  have hp' := one_add_mul_sub_le_pow (show -1 ≤ q by linarith) (3*h-1)
  rw [Nat.cast_sub (by omega : 1 ≤ h)] at hp
  rw [Nat.cast_sub (by omega : 1 ≤ 3*h)] at hp'
  push_cast at hp hp'
  constructor
  · nlinarith only [hx, hp, mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hcoeff)]
  · have h4 : 4 ≤ (h:ℝ) := by exact_mod_cast (show 4 ≤ h by omega)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hcoeff'),
      mul_nonneg (sub_nonneg.mpr h4) (sub_nonneg.mpr hx),
      mul_nonneg (show 0 ≤ (h:ℝ) by positivity) (sub_nonneg.mpr hp')]

private theorem central_row_gain {q : ℝ} {h : ℕ} (a : ℕ → ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (ha : 0 ≤ a h)
    (hrows : ∀ i ∈ range h, a h ≤ a i * q^((h-i)*h)) :
    a h*(h:ℝ)^2*(h+1)*(1-q)/2 ≤ (∑ i ∈ range h, a i)-a h*rowMass q 1 h := by
  have htri : ∑ i ∈ range h, ((h:ℝ)-i) = (h:ℝ)*(h+1)/2 := by
    rw [← sum_succ_cast, ← sum_range_reflect (fun i : ℕ => (i:ℝ)+1) h]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [Nat.cast_sub (by omega : i ≤ h-1), Nat.cast_sub (by omega : 1 ≤ h)]
    push_cast
    ring
  have hbound : ∑ i ∈ range h, (a h+(a h*h*(1-q))*((h:ℝ)-i))
      ≤ ∑ i ∈ range h, a i := by
    apply sum_le_sum
    intro i hi
    have hi' := mem_range.mp hi
    have hb := mul_le_mul_of_nonneg_left (inv_pow_bernoulli hq ((h-i)*h)) ha
    rw [Nat.cast_mul, Nat.cast_sub hi'.le] at hb
    have hr : a h*(1/q)^((h-i)*h) ≤ a i := by
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact (div_le_iff₀ (pow_pos hq _)).mpr (hrows i hi)
    nlinarith only [hb,hr]
  rw [sum_add_distrib, ← mul_sum, htri] at hbound
  simp at hbound
  nlinarith only [hbound,
    mul_nonneg ha (sub_nonneg.mpr (rowMass_le_length hq.le hq1 1 h))]

/-- A central child row product bounds every preceding parent row factor
after the column-weight rescaling a_i = q^i ρ_i. -/
theorem central_prefix_row_bound {q R : ℝ} {h : ℕ} (ρ : ℕ → ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hn : ∀ i ∈ range (h-1), 0 ≤ ρ i)
    (hrows : ∀ i ∈ range (h-1), R ≤ ρ i * q^((h-1-i)*h)) :
    ∀ i ∈ range (h-1), R ≤ q^i * ρ i := by
  intro i hi
  have hi' := mem_range.mp hi
  have hd : i ≤ (h-1-i)*h := by
    have H := Nat.mul_le_mul_right h (show 1 ≤ h-1-i by omega)
    simpa using le_trans (show i ≤ h by omega) (by simpa using H)
  rw [mul_comm]
  exact (hrows i hi).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq hq1 hd) (hn i hi))

/-- The reflected prefix of length h+1 lies under the chord of prefix h-1
and prefix h at odd order m=2*h+1. The last inequality compares the drop
in prefix weight with the slope times the deficit in horizontal coordinate. -/
theorem central_pruning {q R : ℝ} {h : ℕ} (a : ℕ → ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hh : 6 ≤ h) (hR : 0 ≤ R)
    (hrel : a h = R*q^(2*h-1))
    (hpre : ∀ i ∈ range (h-1), R ≤ a i)
    (hrows : ∀ i ∈ range h, a h ≤ a i * q^((h-i)*h))
    (hel : ∑ i ∈ range (h-1), (1/q)^((i+1)*h) ≤ rowMass q 1 h) :
    let B := rowMass q 0 h
    let U := rowMass q (h+1) h
    let T := R*(q^h+U)-∑ i ∈ range (h-1), a i
    rowMass q 0 (h-1) ≤ U ∧ U ≤ B ∧
      T*(B-U) ≤ q^h*((∑ i ∈ range h, a i)-a h*rowMass q 1 h) := by
  dsimp only
  let B := rowMass q 0 h
  let U := rowMass q (h+1) h
  let T := R*(q^h+U)-∑ i ∈ range (h-1), a i
  change rowMass q 0 (h-1) ≤ U ∧ U ≤ B ∧ T*(B-U) ≤ _
  obtain ⟨hfac, hfac'⟩ := central_factors hq hq1 hh (central_parameter hq hq1 hh hel)
  have hU : U = q^(h+1)*B := by
    exact rowMass_shift q (h+1) 0 h
  have hB : B ≤ h := rowMass_le_length hq.le hq1 _ _
  have hUn : U ≤ B := by
    rw [hU]
    exact mul_le_of_le_one_left (sum_nonneg fun i _ => pow_nonneg hq.le _) (pow_le_one₀ hq.le hq1)
  have hgap : B-U ≤ (h:ℝ)*(h+1)*(1-q) := by
    rw [hU]
    have hp := one_add_mul_sub_le_pow (show -1 ≤ q by linarith) (h+1)
    push_cast at hp
    nlinarith only [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr (pow_le_one₀ hq.le hq1 (n := h+1))),
      mul_nonneg (show 0 ≤ (h:ℝ) by positivity) (sub_nonneg.mpr hp)]
  have hBsplit : B = rowMass q 0 (h-1)+q^(h-1) := by
    dsimp [B,rowMass]
    conv_lhs => rw [show h = h-1+1 by omega, sum_range_succ]
    simp
  refine ⟨by linarith, hUn, ?_⟩
  have hT : T ≤ 2*R := by
    have hr : (h-1:ℝ)*R ≤ ∑ i ∈ range (h-1), a i := by
      simpa [Nat.cast_sub (show 1 ≤ h by omega)] using sum_le_sum hpre
    dsimp [T]
    nlinarith only [hr, mul_nonneg hR (sub_nonneg.mpr (hUn.trans hB)),
      mul_nonneg hR (sub_nonneg.mpr (pow_le_one₀ hq.le hq1 (n := h)))]
  have hscale : 4*R ≤ (h:ℝ)*q^h*a h := by
    rw [hrel]
    have he : q^(3*h-1) = q^h * q^(2*h-1) := by rw [← pow_add]; congr 1; omega
    rw [he] at hfac'
    nlinarith only [mul_nonneg hR (sub_nonneg.mpr hfac')]
  have har : 0 ≤ a h := by rw [hrel]; positivity
  have hgain := central_row_gain a hq hq1 har hrows
  nlinarith only [mul_nonneg (sub_nonneg.mpr hUn) (sub_nonneg.mpr hT),
    mul_nonneg hR (sub_nonneg.mpr hgap),
    mul_nonneg (show 0 ≤ (h:ℝ)*(h+1)*(1-q) by positivity) (sub_nonneg.mpr hscale),
    mul_nonneg (pow_nonneg hq.le h) (sub_nonneg.mpr hgain)]


end GeometricMaxCut

namespace GeometricMaxCut

open Finset

noncomputable def prefixWeight (q : ℝ) (n k : ℕ) : ℝ :=
  rowSum q n k * rowMass q k (n-k)

/-- Slope between the prefix points of lengths k and k+1 in order n+1. -/
noncomputable def prefixSlope (q : ℝ) (n k : ℕ) : ℝ :=
  rowFactor q n k * rowMass q (k+1) (n-k) - rowSum q (n+1) k

theorem rowMass_nonneg {q : ℝ} (hq : 0 ≤ q) (s n : ℕ) : 0 ≤ rowMass q s n :=
  sum_nonneg fun _ _ => pow_nonneg hq _

theorem rowSum_nonneg {q : ℝ} (hq : 0 ≤ q) (n k : ℕ) : 0 ≤ rowSum q n k :=
  sum_nonneg fun _ _ => pow_nonneg hq _

theorem rowFactor_nonneg {q : ℝ} (hq : 0 ≤ q) (n k : ℕ) : 0 ≤ rowFactor q n k :=
  pow_nonneg hq _

theorem rowFactor_pos {q : ℝ} (hq : 0 < q) (n k : ℕ) : 0 < rowFactor q n k :=
  pow_pos hq _

theorem prefixWeight_step (q : ℝ) {n k : ℕ} (hk : k < n) :
    prefixWeight q (n+1) (k+1) - prefixWeight q (n+1) k = q^k * prefixSlope q n k := by
  unfold prefixWeight prefixSlope
  rw [rowSum_last, rowFactor_parent q hk, Nat.add_sub_add_right]
  have hs := rowMass_add q k 1 (n-k)
  rw [show 1+(n-k) = n+1-k by omega] at hs
  simp [rowMass] at hs
  rw [← show q^k + rowMass q (k+1) (n-k) = rowMass q k (n+1-k) by exact hs.symm]
  ring

theorem prefixSlope_antitone {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) {n i j : ℕ}
    (hij : i ≤ j) (hj : j < n) : prefixSlope q n j ≤ prefixSlope q n i := by
  have hrow : rowFactor q n j ≤ rowFactor q n i := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j hi ih =>
      have hstep := rowFactor_step q (by omega : j < n)
      rw [hstep]
      exact (mul_le_of_le_one_right (rowFactor_nonneg hq _ _) (pow_le_one₀ hq hq1)).trans
        (ih (by omega))
  have tail : rowMass q (j+1) (n-j) ≤ rowMass q (i+1) (n-i) := by
    have hs := rowMass_add q (i+1) (j-i) (n-j)
    rw [show (j-i)+(n-j) = n-i by omega, show i+1+(j-i) = j+1 by omega] at hs
    linarith [rowMass_nonneg hq (i+1) (j-i)]
  have partialS : rowSum q (n+1) i ≤ rowSum q (n+1) j :=
    sum_le_sum_of_subset_of_nonneg (range_mono hij)
      fun k _ _ => rowFactor_nonneg hq _ _
  exact sub_le_sub (mul_le_mul hrow tail (rowMass_nonneg hq _ _) (rowFactor_nonneg hq _ _)) partialS

theorem scaled_prefix (q : ℝ) {n k : ℕ} (hk : k ≤ n) :
    q * geomCut q (prefixWord n k false) = prefixWeight q n k := prefix_cut q hk

theorem eligible_of_nonneg_slope {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    {n k : ℕ} (hk : k+1 ≤ (n+1)/2) (hs : 0 ≤ prefixSlope q n k) :
    Eligible q (n+1) (k+1) := by
  refine ⟨hk, ?_⟩
  intro i hi
  apply le_of_mul_le_mul_left (a := q) _ hq
  rw [scaled_prefix q (by omega : i ≤ n+1), scaled_prefix q (by omega : k+1 ≤ n+1)]
  have walk : ∀ j, i ≤ j → j ≤ k+1 → prefixWeight q (n+1) i ≤ prefixWeight q (n+1) j := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; rfl
    | succ j hji ih =>
      intro hj
      have hs' := hs.trans (prefixSlope_antitone hq.le hq1 (show j ≤ k by omega) (by omega))
      have hw := prefixWeight_step q (show j < n by omega)
      exact (ih (by omega)).trans (by nlinarith [mul_nonneg (pow_nonneg hq.le j) hs'])
  exact walk _ hi le_rfl

theorem slope_of_eligible {q : ℝ} (hq : 0 < q) {n k : ℕ}
    (hk : Eligible q (n+1) (k+1)) : 0 ≤ prefixSlope q n k := by
  have hs := hk.2 k (by omega)
  have hb := hk.1
  have hw := mul_le_mul_of_nonneg_left hs hq.le
  rw [scaled_prefix q (by omega : k ≤ n+1),scaled_prefix q (by omega : k+1 ≤ n+1)] at hw
  have hs' := prefixWeight_step q (show k < n by omega)
  exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ q^k * prefixSlope q n k) (pow_pos hq _)

theorem zero_eligible (q : ℝ) (n : ℕ) : Eligible q n 0 :=
  ⟨Nat.zero_le _, fun j hj => by cases Nat.eq_zero_of_le_zero hj; rfl⟩

theorem eligible_down {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) {n h k : ℕ}
    (hk : Eligible q n k) (hh : h ≤ k) : Eligible q n h := by
  cases h with
  | zero => exact zero_eligible q n
  | succ h =>
    have hb := hk.1
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    apply eligible_of_nonneg_slope hq hq1 (by omega)
    exact (slope_of_eligible hq hk).trans (prefixSlope_antitone hq.le hq1 (by omega) (by omega))

/-- Consecutive child prefix comparison in the row coordinates used by
the analytic lemmas. The child has h+L vertices and the parent has one more. -/
theorem child_eligibility {q : ℝ} (hq : 0 < q) {h L : ℕ} (hh : 1 ≤ h)
    (hel : Eligible q (h+L) h) :
    (∑ i ∈ range (h-1), rowFactor q (h+L) i) ≤
      rowFactor q (h+L) (h-1) * rowMass q 1 L := by
  have hB := hel.1
  let n := h+L-1
  have hn : n+1 = h+L := by dsimp [n]; omega
  have hs : 0 ≤ prefixSlope q n (h-1) := by
    apply slope_of_eligible hq
    rwa [hn, show h-1+1 = h by omega]
  unfold prefixSlope at hs
  rw [show h-1+1 = h by omega, show n-(h-1) = L by dsimp [n]; omega, hn] at hs
  have ht : rowMass q h L = q^(h-1)*rowMass q 1 L := by
    simpa only [show h-1+1 = h by omega] using rowMass_shift q (h-1) 1 L
  have hrow := rowFactor_parent q (by dsimp [n]; omega : h-1 < n)
  rw [hn] at hrow
  rw [ht] at hs
  rw [hrow]
  change rowSum q (h+L) (h-1) ≤ _
  nlinarith only [hs]

end GeometricMaxCut

namespace GeometricMaxCut

open Finset

/-- A point underneath the secant of two cut words; the vertical scale is q. -/
def WordChord (q : ℝ) (lo w hi : List Bool) : Prop :=
  geomMass q lo ≤ geomMass q w ∧ geomMass q w ≤ geomMass q hi ∧ ∃ s : ℝ,
    q*(geomCut q hi-geomCut q lo) = s*(geomMass q hi-geomMass q lo) ∧
    s*(geomMass q hi-geomMass q w) ≤ q*(geomCut q hi-geomCut q w)

theorem prefix_reflected_mass (q : ℝ) {n h : ℕ} (hh : h ≤ n) :
    geomMass q (prefixWord n h true) = rowMass q h (n-h) := by
  rw [← prefixWord_compl,geomMass_compl,prefixWord_length hh,prefix_mass,geomTotal_rowMass]
  have H := rowMass_add q 0 h (n-h)
  rw [show h+(n-h) = n by omega, Nat.zero_add] at H
  linarith

theorem block_mass (q : ℝ) (h L : ℕ) :
    geomMass q (false :: prefixWord (h+L) h false) = q*rowMass q 0 h := by
  simp [geomMass,prefix_mass]

theorem block_cut (q : ℝ) {h L : ℕ} (hh : 0 < h) :
    q*geomCut q (false :: prefixWord (h+L) h false) =
      q*rowMass q 0 h + (rowSum q (h+L+1) (h+1)-1)*rowMass q (h+1) L := by
  have H := prefix_cut q (show h ≤ h+L by omega)
  simp only [Nat.add_sub_cancel_left] at H
  rw [geomCut,prefixWord_length (by omega : h ≤ h+L),prefix_mass,rowSum_cons]
  simp only [Bool.false_eq_true,if_false]
  have HU : rowMass q (h+1) L = q*rowMass q h L := by
    simpa only [Nat.add_comm 1 h, pow_one] using rowMass_shift q 1 h L
  have HP : q^(h+L) = q^(h+L-1)*q := by rw [← pow_succ]; congr 1; omega
  rw [HU,HP]
  nlinarith only [congrArg (fun y : ℝ => q^(h+L-1)*q*y) H]

theorem rowMass_last (q : ℝ) (h : ℕ) :
    rowMass q 0 (h+1) = rowMass q 0 h + q^h := by simp [rowMass,sum_range_succ]

theorem rowMass_gap (q : ℝ) (h : ℕ) :
    rowMass q 0 h - q*rowMass q 0 h = 1-q^h := by
  have H := geom_sum_mul q h
  simpa only [rowMass,zero_add] using (show (∑ i ∈ range h, q^i)-q*(∑ i ∈ range h, q^i) =
    1-q^h by nlinarith only [H])

theorem prefix_slope_word (q : ℝ) {n h : ℕ} (hh : 1 ≤ h) (hn : h ≤ n) :
    q*(geomCut q (prefixWord (n+1) h false)-geomCut q (prefixWord (n+1) (h-1) false)) =
    prefixSlope q n (h-1) *
      (geomMass q (prefixWord (n+1) h false)-geomMass q (prefixWord (n+1) (h-1) false)) := by
  rw [mul_sub,scaled_prefix q (by omega : h ≤ n+1),scaled_prefix q (by omega : h-1 ≤ n+1),
    prefix_mass,prefix_mass]
  have hm := rowMass_last q (h-1)
  have hs := prefixWeight_step q (by omega : h-1 < n)
  rw [show h-1+1 = h by omega] at hs hm
  rw [hs,hm]
  ring

theorem concrete_row_decay {q : ℝ} {h L : ℕ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ i ∈ range (h-1), rowFactor q (h+L) (h-1) ≤
      rowFactor q (h+L) i * q^((h-1-i)*L) := by
  apply row_decay_of_step (h := h) (L := L) (rowFactor q (h+L)) hq hq1 (fun i _ => rowFactor_nonneg hq _ _)
  intro i hi
  exact rowFactor_step q (show i < h+L by omega)

theorem concrete_inverse {q : ℝ} {h L : ℕ} (hq : 0 < q) (hq1 : q ≤ 1) (hh : 1 ≤ h)
    (he : Eligible q (h+L) h) :
    ∑ i ∈ range (h-1), (1/q)^((i+1)*L) ≤ rowMass q 1 L :=
  inverse_eligibility _ hq (rowFactor_pos hq _ _) (concrete_row_decay hq.le hq1)
    (child_eligibility hq hh he)

theorem noncentral_word_mass {q : ℝ} {h L : ℕ} (hq : 4/5 ≤ q) (hq1 : q ≤ 1)
    (hh : 1 ≤ h) (hl : h < L) (hm : 12 ≤ h+L+1) (he : Eligible q (h+L) h) :
    geomMass q (prefixWord (h+L+1) h false) ≤
      geomMass q (prefixWord (h+L+1) (h+1) true) := by
  rw [prefix_mass,prefix_reflected_mass q (by omega : h+1 ≤ h+L+1),
    show h+L+1-(h+1) = L by omega]
  exact noncentral_pruning hq hq1 hh hl hm (concrete_inverse (by linarith) hq1 hh he)

theorem last_prefix_slope (q : ℝ) {h L : ℕ} (hh : 1 ≤ h) :
    prefixSlope q (h+L) (h-1) =
    rowFactor q (h+L) (h-1) * (q^h+rowMass q (h+1) L) - rowSum q (h+L+1) (h-1) := by
  unfold prefixSlope
  rw [show h-1+1 = h by omega, show h+L-(h-1) = 1+L by omega, rowMass_add]
  simp [rowMass]

theorem central_prefix_difference (q : ℝ) (h L : ℕ) (hL : 0 < L) :
    q*(geomCut q (prefixWord (h+L+1) h false)-geomCut q (prefixWord (h+L+1) (h+1) true)) =
      q^h*(rowSum q (h+L+1) h - rowFactor q (h+L+1) h * rowMass q 1 L) := by
  rw [geomCut_prefix_compl,mul_sub,scaled_prefix q (by omega : h ≤ h+L+1),
    scaled_prefix q (by omega : h+1 ≤ h+L+1)]
  have hs := prefixWeight_step q (show h < h+L by omega)
  unfold prefixSlope at hs
  rw [show h+L-h = L by omega,rowMass_shift q h 1 L] at hs
  rw [rowFactor_parent q (show h < h+L by omega)]
  nlinarith only [hs]

theorem central_word_chord {q : ℝ} {h : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 6 ≤ h) (he : Eligible q (h+h) h) :
    WordChord q (prefixWord (h+h+1) (h-1) false) (prefixWord (h+h+1) (h+1) true)
      (prefixWord (h+h+1) h false) := by
  let a := rowFactor q (h+h+1)
  let ρ := rowFactor q (h+h)
  let R := ρ (h-1)
  have hprod := concrete_row_decay (h := h) (L := h) hq.le hq1
  have hrel : a h = R*q^(2*h-1) := by
    have hp := rowFactor_step q (show h-1 < h+h+1 by omega)
    rw [show h-1+1 = h by omega, show h+h+1-(h-1)-2 = h by omega,
      rowFactor_parent q (show h-1 < h+h by omega)] at hp
    change rowFactor q (h+h+1) h = rowFactor q (h+h) (h-1)*q^(2*h-1)
    rw [hp, show 2*h-1 = (h-1)+h by omega, pow_add]
    ring
  have hpre : ∀ i ∈ range (h-1), R ≤ a i := by
    intro i hi
    have hi' := mem_range.mp hi
    change R ≤ rowFactor q (h+h+1) i
    rw [rowFactor_parent q (show i < h+h by omega)]
    exact central_prefix_row_bound ρ hq.le hq1 (fun j _ => rowFactor_nonneg hq.le _ _) hprod i hi
  have hrows : ∀ i ∈ range h, a h ≤ a i*q^((h-i)*h) := by
    have hw := row_decay_of_step (h := h+1) (L := h) a hq.le hq1
      (fun j _ => rowFactor_nonneg hq.le _ _)
      (by
        intro i hi
        change rowFactor q (h+h+1) (i+1) = _
        rw [rowFactor_step q (show i < h+h+1 by omega)]
        dsimp only [a]
        congr 2
        omega)
    simpa only [Nat.add_sub_cancel] using hw
  have hwin := central_pruning a hq hq1 hh (rowFactor_nonneg hq.le _ _) hrel hpre hrows
    (concrete_inverse hq hq1 (by omega) he)
  dsimp only at hwin
  obtain ⟨hlo,hhi,hsec⟩ := hwin
  unfold WordChord
  simp only [prefix_mass,prefix_reflected_mass q (by omega : h+1 ≤ h+h+1),
    show h+h+1-(h+1) = h by omega]
  refine ⟨hlo,hhi, prefixSlope q (h+h) (h-1), ?_, ?_⟩
  · simpa [prefix_mass] using prefix_slope_word q (n := h+h) (h := h) (by omega) (by omega)
  · rw [last_prefix_slope q (by omega : 1 ≤ h),central_prefix_difference q h h (by omega)]
    exact hsec

private theorem child_power_bound {q : ℝ} {h L : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 2 ≤ h) (hl : h ≤ L) (he : Eligible q (h+L) h) :
    (2/3:ℝ) ≤ q^(h-1) := by
  have hi : h-2 ∈ range (h-1) := mem_range.mpr (by omega)
  have hle := single_le_sum (s := range (h-1))
    (f := fun i => (1/q)^((i+1)*L)) (fun i _ => by positivity) hi
  have hr := hle.trans ((concrete_inverse hq hq1 (by omega) he).trans
    (rowMass_le_length hq.le hq1 1 L))
  rw [show h-2+1 = h-1 by omega, one_div, inv_pow, pow_mul, ← one_div] at hr
  have hb := (div_le_iff₀ (pow_pos (pow_pos hq _) _)).mp hr
  by_contra! hbad
  have hL0 : 0 < (L:ℝ) := by exact_mod_cast (show 0 < L by omega)
  have H := mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ hbad (pow_nonneg hq.le _) (by omega : L ≠ 0)) hL0
  linarith [geometric_decay L (by omega)]

private theorem block_middle_sum (q : ℝ) {h L : ℕ} (hh : 2 ≤ h) :
    ∑ i ∈ range (h-2), q^(1+i)*(1-rowFactor q (h+L) (i+1)) =
    rowMass q 0 (h-1) - rowSum q (h+L+1) (h-1) := by
  have hid : ∀ i ∈ range (h-2), q^(1+i)*(1-rowFactor q (h+L) (i+1)) =
      q^(i+1)-rowFactor q (h+L+1) (i+1) := by
    intro i hi
    have hi' := mem_range.mp hi
    rw [rowFactor_parent q (show i+1 < h+L by omega), Nat.add_comm 1 i]
    ring
  rw [sum_congr rfl hid, sum_sub_distrib]
  unfold rowMass rowSum
  conv_rhs => rw [show h-1 = (h-2)+1 by omega, sum_range_succ', sum_range_succ']
  simp [rowFactor,rowExp]

private theorem last_row_relation (q : ℝ) {h L : ℕ} (hh : 1 ≤ h) (hl : 1 ≤ L) :
    rowFactor q (h+L+1) h = rowFactor q (h+L) (h-1)*q^h*q^(L-1) := by
  have hs := rowFactor_step q (show h-1 < h+L+1 by omega)
  rw [show h-1+1 = h by omega, show h+L+1-(h-1)-2 = L by omega,
    rowFactor_parent q (show h-1 < h+L by omega)] at hs
  rw [hs]
  have hp : q^(h-1)*q^L = q^h*q^(L-1) := by rw [← pow_add, ← pow_add]; congr 1; omega
  nlinarith only [congrArg (fun y : ℝ => rowFactor q (h+L) (h-1)*y) hp]

/-- The feasible chord for the nonmonotone child extension, in raw cut-word
coordinates. This is the one-hole case for the HullAt induction. -/
theorem block_word_chord {q : ℝ} {h L : ℕ} (hq : 4/5 ≤ q) (hq1 : q ≤ 1)
    (hh : 2 ≤ h) (hl : h ≤ L) (hm : 12 ≤ h+L+1) (he : Eligible q (h+L) h) :
    WordChord q (prefixWord (h+L+1) (h-1) false) (false :: prefixWord (h+L) h false)
      (prefixWord (h+L+1) h false) := by
  have hq0 : 0 < q := by linarith
  let n := h+L
  let R := rowFactor q n (h-1)
  let G := rowMass q (h+1) L
  let V := rowMass q 0 (h-1)
  let A := rowSum q (n+1) (h-1)
  have hwin := eligibleBlockChord (R := R) (rowFactor q n) hq hq1 hh hl hm
    (rowFactor_pos hq0 _ _) (by simp [n,rowFactor,rowExp])
    (fun i _ => rowFactor_nonneg hq0.le _ _)
    (concrete_row_decay hq0.le hq1) (child_eligibility hq0 (by omega) he)
  change 0 ≤ G*(1-R+R*q^h*(1-q^(L-1)))
      - (∑ i ∈ range (h-2), q^(1+i)*(1-rowFactor q (h+L) (i+1)))
      -(q^(h-1)+q^h-1)*(1-R*q^h) at hwin
  rw [block_middle_sum q hh] at hwin
  change 0 ≤ G*(1-R+R*q^h*(1-q^(L-1)))-(V-A)-(q^(h-1)+q^h-1)*(1-R*q^h) at hwin
  have hv := rowMass_last q (h-1)
  rw [show h-1+1 = h by omega] at hv
  change rowMass q 0 h = V+q^(h-1) at hv
  have hb := rowMass_gap q h
  have hp := child_power_bound hq0 hq1 hh hl he
  have hqh : q^h = q^(h-1)*q := by rw [← pow_succ]; congr 1; omega
  have massLo : V ≤ q*rowMass q 0 h := by
    nlinarith only [hv,hb,hqh,hp,mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq),hq]
  have massHi : q*rowMass q 0 h ≤ rowMass q 0 h := by
    exact mul_le_of_le_one_left (rowMass_nonneg hq0.le _ _) hq1
  unfold WordChord
  simp only [prefix_mass,block_mass]
  refine ⟨massLo,massHi,prefixSlope q n (h-1), ?_, ?_⟩
  · simpa [prefix_mass,n] using prefix_slope_word q (n := h+L) (h := h) (by omega) (by omega)
  · rw [mul_sub q, prefix_cut q (by omega : h ≤ h+L+1),block_cut q (by omega : 0 < h)]
    have hrem : rowMass q h (h+L+1-h) = q^h+G := by
      rw [show h+L+1-h = 1+L by omega,rowMass_add]
      simp [rowMass,G]
    rw [hrem]
    have hA : rowSum q (n+1) h = A+q^(h-1)*R := by
      have hs := rowSum_last q (n+1) (h-1)
      rw [show h-1+1 = h by omega,rowFactor_parent q (show h-1 < n by dsimp [n]; omega)] at hs
      exact hs
    have hAn : rowSum q (n+1) (h+1) = (A+q^(h-1)*R)+R*q^h*q^(L-1) := by
      rw [rowSum_last,hA]
      exact congrArg (fun y => (A+q^(h-1)*R)+y) (last_row_relation q (by omega) (by omega))
    have hT : prefixSlope q n (h-1) = R*(q^h+G)-A := last_prefix_slope q (by omega)
    change prefixSlope q n (h-1) * (rowMass q 0 h - q * rowMass q 0 h) ≤
      rowSum q (n+1) h*(q^h+G) - (q*rowMass q 0 h + (rowSum q (n+1) (h+1)-1)*G)
    rw [hT,hA,hAn,hb]
    have hmass : q*rowMass q 0 h = V+q^(h-1)-(1-q^h) := by linarith
    rw [hmass]
    nlinarith only [hwin]


end GeometricMaxCut

namespace GeometricMaxCut

theorem mass_bounds {q : ℝ} (hq : 0 ≤ q) (w : List Bool) :
    0 ≤ geomMass q w ∧ geomMass q w ≤ geomTotal q w.length := by
  induction w with
  | nil => simp [geomMass, geomTotal]
  | cons b w ih =>
    have h := mul_le_mul_of_nonneg_left ih.2 hq
    have hp := mul_nonneg hq ih.1
    cases b <;> simp [geomMass,geomTotal_succ] <;> constructor <;> linarith

theorem total_bound {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    geomTotal q n ≤ n := by
  induction n with
  | zero => simp [geomTotal,geomMass]
  | succ n ih =>
    rw [geomTotal_succ, Nat.cast_succ]
    have ht : 0 ≤ geomTotal q n := (mass_bounds hq (List.replicate n true)).1
    linarith [mul_le_mul_of_nonneg_right hq1 ht]

theorem coarse_incidence {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (w : List Bool) :
    q * geomCut q w ≤ (w.length : ℝ) * geomMass q w := by
  induction w with
  | nil => simp [geomMass,geomCut]
  | cons b w ih =>
    by_cases hlen : w.length = 0
    · have : w = [] := List.length_eq_zero_iff.mp hlen
      subst w
      cases b <;> simp [geomMass,geomCut,geomTotal]
    have hp := pow_le_pow_of_le_one hq hq1 (show 1 ≤ w.length by omega)
    rw [pow_one] at hp
    have hm := (mass_bounds hq w).1
    have hp0 : 0 ≤ q^w.length := pow_nonneg hq _
    have h1 := mul_le_mul_of_nonneg_left ih hp0
    have h2 := mul_le_mul_of_nonneg_right hp (mul_nonneg (Nat.cast_nonneg w.length) hm)
    have h3 := mul_le_mul_of_nonneg_left (total_bound hq hq1 w.length) hq
    have h4 := mul_le_mul_of_nonneg_right hq1 (Nat.cast_nonneg w.length : 0 ≤ (w.length : ℝ))
    cases b <;> simp only [List.length_cons,Nat.cast_add_one,geomCut,geomMass,
      Bool.false_eq_true,if_false,if_true,zero_add] <;> nlinarith [mul_nonneg hq hm]

theorem geomTotal_identity (q : ℝ) (n : ℕ) :
    (1-q) * geomTotal q n = 1-q^n := by
  induction n with
  | zero => simp [geomTotal,geomMass]
  | succ n ih => rw [geomTotal_succ,pow_succ]; nlinarith [congrArg (fun a : ℝ => q*a) ih]

theorem first_row_bound {q : ℝ} (hq : 0 ≤ q) (hu : q ≤ 4/5) (L : ℕ) :
    q^(L+1)*geomTotal q L ≤ 1 := by
  have hpos : 0 < 1-q := by linarith
  apply le_of_mul_le_mul_left (a := 1-q) _ hpos
  rw [pow_succ]
  have hh := geomTotal_identity q L
  have hx := mul_le_mul_of_nonneg_left (sq_nonneg (2*q^L-1)) hq
  nlinarith [congrArg (fun x : ℝ => (q^L*q)*x) hh]

theorem tail_six {q : ℝ} (hq : 0 < q) (hu : q ≤ 4/5) (b : Bool) (v : List Bool)
    (hv : v.length = 5) :
    q^6 * geomCut q (b::v) ≤ geomMass q (b::v) := by
  have hc := coarse_incidence hq.le (by linarith : q ≤ 1) v
  rw [hv] at hc
  norm_num at hc
  have hpower (i : ℕ) : q^i ≤ (4/5 : ℝ)^i := pow_le_pow_left₀ hq.le hu _
  have hsum : q^5+5*q^9 ≤ 1 := by nlinarith [hpower 5,hpower 9]
  have hm := (mass_bounds hq.le v).1
  have hA := mul_le_mul_of_nonneg_left hc (pow_nonneg hq.le 10)
  have hB := mul_le_mul_of_nonneg_right hsum (mul_nonneg hq.le hm)
  have ht := first_row_bound hq.le hu 5
  norm_num at ht
  cases b <;> simp only [geomCut,geomMass,hv,Bool.false_eq_true,if_false,if_true,zero_add] <;>
    nlinarith [mul_nonneg (pow_nonneg hq.le 6) hm]

theorem tail_absorbed {q : ℝ} (hq : 0 < q) (hu : q ≤ 4/5) (w : List Bool)
    (hw : 6 ≤ w.length) : q^w.length * geomCut q w ≤ geomMass q w := by
  induction w with
  | nil => simp at hw
  | cons b v ih =>
    simp only [List.length_cons] at hw ⊢
    by_cases hv : v.length = 5
    · simpa [hv] using tail_six hq hu b v hv
    have hlen : 6 ≤ v.length := by omega
    have hc := ih hlen
    have hm := (mass_bounds hq.le v).1
    have ht := first_row_bound hq.le hu v.length
    have hh : q^v.length ≤ (4/5 : ℝ)^6 :=
      (pow_le_pow_of_le_one hq.le (by linarith) hlen).trans (pow_le_pow_left₀ hq.le hu _)
    have hp : 2*q^v.length ≤ 1 := by norm_num at hh; linarith
    have hP := mul_le_mul_of_nonneg_right hp (mul_nonneg hq.le hm)
    have hR := mul_le_mul_of_nonneg_left hc (pow_nonneg hq.le (v.length+1))
    cases b <;> simp only [geomCut,geomMass,Bool.false_eq_true,if_false,if_true,zero_add]
    · rw [pow_succ] at hR ⊢
      nlinarith
    · nlinarith [mul_nonneg hq.le hm]

theorem false_zero (q : ℝ) (n : ℕ) :
    geomMass q (List.replicate n false) = 0 ∧ geomCut q (List.replicate n false) = 0 := by
  induction n with
  | zero => simp [geomMass,geomCut]
  | succ n ih => simp [List.replicate_succ,geomMass,geomCut,ih]

theorem small_q_all_words {q : ℝ} (hq : 0 < q) (hu : q ≤ 4/5) (w : List Bool)
    (hw : 7 ≤ w.length) : geomCut q w ≤ geomCut q (prefixWord w.length 1 false) := by
  cases w with
  | nil => simp at hw
  | cons b v =>
    have hlen : 6 ≤ v.length := by simp at hw; omega
    have canon : geomCut q (prefixWord (b::v).length 1 false) = geomTotal q v.length := by
      simp [prefixWord,geomCut,false_zero]
    rw [canon]
    cases b
    · have e := geomCut_compl q (false::v)
      have h := tail_absorbed hq hu (v.map Bool.not) (by simpa using hlen)
      rw [←e]
      simp only [List.map_cons,Bool.not_false,geomCut,if_true,List.length_map]
      simp only [List.length_map] at h
      linarith
    · have h := tail_absorbed hq hu v hlen
      simp only [geomCut,if_true]
      linarith

end GeometricMaxCut

namespace GeometricMaxCut

open OMA.S_arxiv_2603_08876

theorem singleton_wins {q : ℝ} (hq : 0 < q) (hu : q ≤ 4/5) {n : ℕ} (hn : 7 ≤ n)
    (S : Finset (Fin n)) : cutWeight n q⁻¹ S ≤ cutWeight n q⁻¹ (isolatedCut n 1) := by
  let w := List.ofFn (fun i : Fin n => decide (i ∈ S))
  have hL : w.length = n := List.length_ofFn
  have h := small_q_all_words hq hu w (by omega)
  rw [hL, ←prefix_source (show 1 ≤ n by omega), cast_source q hq (isolatedCut n 1)] at h
  change geomCut q (List.ofFn fun i => decide (i ∈ S)) ≤ _ at h
  rw [cast_source q hq S] at h
  exact le_of_mul_le_mul_left h (pow_pos hq _)

theorem singleton_range {n : ℕ} (hn : 7 ≤ n) {r : ℝ} (hr : 5/4 ≤ r) :
    ∀ S : Finset (Fin n), cutWeight n r S ≤ cutWeight n r (isolatedCut n 1) := by
  have hr0 : 0 < r := by linarith
  have hq : r⁻¹ ≤ 4/5 := (inv_le_iff_one_le_mul₀ hr0).mpr (by linarith)
  simpa using singleton_wins (inv_pos.mpr hr0) hq hn

theorem source_of_induction
    (base : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → ∀ q : ℝ, 4/5 ≤ q → q < 1 → HullAt q n)
    (step : ∀ n : ℕ, 11 ≤ n → ∀ q : ℝ, 4/5 ≤ q → q < 1 → HullAt q n → HullAt q (n+1)) :
    ∀ n : ℕ, 7 ≤ n → ∀ r : ℝ, 1 < r → r < 2 →
      ∃ k, 1 ≤ k ∧ k ≤ n/2 ∧ ∀ S : Finset (Fin n),
        cutWeight n r S ≤ cutWeight n r (isolatedCut n k) := by
  intro n hn r hr _
  have hr0 : 0 < r := by linarith
  by_cases hi : 5/4 ≤ r
  · exact ⟨1, le_rfl, by omega, singleton_range hn hi⟩
  have hq : 4/5 ≤ r⁻¹ := by
    apply le_of_mul_le_mul_left (a := r) _ hr0
    rw [mul_inv_cancel₀ hr0.ne']
    linarith
  have hq1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have H : ∀ m, 7 ≤ m → HullAt r⁻¹ m := by
    intro m
    induction m with
    | zero => omega
    | succ m ih =>
      intro hm
      by_cases hsmall : m+1 ≤ 11
      · exact base _ hm hsmall _ hq hq1
      · exact step _ (by omega) _ hq hq1 (ih (by omega))
  simpa using conclusion_of_hull (show 2 ≤ n by omega) (inv_pos.mpr hr0) (H n hn)

end GeometricMaxCut

namespace GeometricMaxCut

open Finset

def Covered (q : ℝ) (n : ℕ) (w : List Bool) : Prop :=
  ∀ t : ℝ, ∃ j rev, Eligible q n j ∧ score q t w ≤ score q t (prefixWord n j rev)

theorem covered_of_eligible {q : ℝ} {n k : ℕ} (h : Eligible q n k) (rev : Bool) :
    Covered q n (prefixWord n k rev) := fun _ => ⟨k,rev,h,le_rfl⟩

theorem score_reflect (q t : ℝ) (w : List Bool) :
    score q t (w.map Bool.not) = score q (-t) w + t*geomTotal q w.length := by
  simp only [score,geomMass_compl,geomCut_compl]
  ring

theorem covered_reflect {q : ℝ} {n : ℕ} {w : List Bool} (len : w.length = n)
    (hw : Covered q n w) : Covered q n (w.map Bool.not) := by
  intro t
  obtain ⟨k,rev,hk,h⟩ := hw (-t)
  refine ⟨k,!rev,hk,?_⟩
  have hr : (prefixWord n k rev).map Bool.not = prefixWord n k (!rev) := by
    cases rev <;> simp [prefixWord,List.map_replicate]
  rw [←hr,score_reflect,score_reflect,len,prefixWord_length (by have := hk.1; omega)]
  linarith

theorem covered_chord {q : ℝ} {n : ℕ} {u v w : List Bool} {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hm : geomMass q w = (1-a)*geomMass q u + a*geomMass q v)
    (hc : geomCut q w ≤ (1-a)*geomCut q u + a*geomCut q v)
    (hu : Covered q n u) (hv : Covered q n v) : Covered q n w := by
  intro t
  have hs : score q t w ≤ (1-a)*score q t u + a*score q t v := by
    unfold score
    rw [hm]
    linarith only [hc]
  rcases le_total (score q t u) (score q t v) with h | h
  · have hp := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr ha1)
    obtain ⟨j,rev,hj,hv'⟩ := hv t
    exact ⟨j,rev,hj,(show score q t w ≤ score q t v by nlinarith only [hs,hp]).trans hv'⟩
  · have hp := mul_le_mul_of_nonneg_left h ha
    obtain ⟨j,rev,hj,hu'⟩ := hu t
    exact ⟨j,rev,hj,(show score q t w ≤ score q t u by nlinarith only [hs,hp]).trans hu'⟩

/-- Every shorter prefix and its reflection have mass on opposite sides of this prefix.
Pick a height maximizer among the shorter prefixes and this prefix. -/
theorem prefix_compression {q : ℝ} (hq : 0 ≤ q) {n j : ℕ} (hj : j ≤ n/2)
    (hspan : ∀ i < j, rowMass q 0 i + rowMass q 0 j ≤ geomTotal q n) :
    Covered q n (prefixWord n j false) := by
  classical
  let ks := Icc 0 j
  have hne : ks.Nonempty := ⟨j,mem_Icc.mpr ⟨Nat.zero_le _,le_rfl⟩⟩
  obtain ⟨k,hk,hbest⟩ := exists_max_image ks (fun k => geomCut q (prefixWord n k false)) hne
  have hkj := (mem_Icc.mp hk).2
  have he : Eligible q n k := ⟨hkj.trans hj,fun i hi => hbest i
    (mem_Icc.mpr ⟨Nat.zero_le _,hi.trans hkj⟩)⟩
  by_cases hsame : k = j
  · subst j
    exact covered_of_eligible he false
  have hc := hbest j (mem_Icc.mpr ⟨Nat.zero_le _,le_rfl⟩)
  have hs := hspan k (by omega)
  intro t
  by_cases ht : 0 ≤ t
  · refine ⟨k,true,he,?_⟩
    rw [←prefixWord_compl,score,score,geomMass_compl,geomCut_compl,
        prefixWord_length (by omega : k ≤ n), prefix_mass,prefix_mass]
    exact add_le_add hc (mul_le_mul_of_nonneg_left (by linarith only [hs]) ht)
  · refine ⟨k,false,he,?_⟩
    rw [score,score,prefix_mass,prefix_mass]
    apply add_le_add hc
    exact mul_le_mul_of_nonpos_left (rowMass_mono_length hq 0 hkj) (le_of_not_ge ht)

theorem compressed_through {q : ℝ} (hq : 0 ≤ q) {n j h : ℕ} (hh : h ≤ n/2)
    (hj : j ≤ h) (hspan : rowMass q 0 (h-1) + rowMass q 0 h ≤ geomTotal q n) :
    Covered q n (prefixWord n j false) := by
  apply prefix_compression hq (hj.trans hh)
  intro i hi
  apply le_trans _ hspan
  exact add_le_add (rowMass_mono_length hq 0 (by omega)) (rowMass_mono_length hq 0 hj)

theorem child_diagram {q : ℝ} (hq : 0 < q) {n : ℕ} (ih : HullAt q n)
    (children : ∀ h, Eligible q n h →
      Covered q (n+1) (true :: prefixWord n h false) ∧
      Covered q (n+1) (false :: prefixWord n h false)) : HullAt q (n+1) := by
  apply hull_succ hq ih
  intro b h rev he
  change Covered q (n+1) (b :: prefixWord n h rev)
  have hh : h ≤ n := by have := he.1; omega
  obtain ⟨hc,hb⟩ := children h he
  cases rev
  · cases b <;> assumption
  · cases b
    · simpa only [List.map_cons,Bool.not_true,prefixWord_compl] using
        covered_reflect (by simp [prefixWord_length hh] : (true :: prefixWord n h false).length = n+1) hc
    · simpa only [List.map_cons,Bool.not_false,prefixWord_compl] using
        covered_reflect (by simp [prefixWord_length hh] : (false :: prefixWord n h false).length = n+1) hb

theorem covered_slope_chord {q s : ℝ} (hq : 0 < q) {n : ℕ} {lo hi w : List Bool}
    (hlo : geomMass q lo ≤ geomMass q w) (hhi : geomMass q w ≤ geomMass q hi)
    (heq : q*(geomCut q hi - geomCut q lo) = s*(geomMass q hi - geomMass q lo))
    (hbelow : s*(geomMass q hi - geomMass q w) ≤ q*(geomCut q hi - geomCut q w))
    (cLo : Covered q n lo) (cHi : Covered q n hi) : Covered q n w := by
  intro t
  by_cases h : 0 ≤ s + q*t
  · obtain ⟨j,rev,hj,hs⟩ := cHi t
    refine ⟨j,rev,hj,le_trans ?_ hs⟩
    apply le_of_mul_le_mul_left (a := q) _ hq
    unfold score
    nlinarith only [hbelow,mul_nonneg h (sub_nonneg.mpr hhi)]
  · obtain ⟨j,rev,hj,hs⟩ := cLo t
    refine ⟨j,rev,hj,le_trans ?_ hs⟩
    apply le_of_mul_le_mul_left (a := q) _ hq
    unfold score
    nlinarith only [heq,hbelow,mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (sub_nonneg.mpr hlo)]

end GeometricMaxCut

namespace GeometricMaxCut

theorem prefix_cons_true (n h : ℕ) :
    true :: prefixWord n h false = prefixWord (n+1) (h+1) false := by
  simp [prefixWord,List.replicate_succ]

theorem prefix_one_cut (q : ℝ) (n : ℕ) :
    geomCut q (prefixWord (n+1) 1 false) = geomTotal q n := by
  simp [prefixWord,geomCut,false_zero]

theorem prefix_two_covered {q : ℝ} (hq : 4/5 ≤ q) {n : ℕ} (hn : 4 ≤ n) {j : ℕ} (hj : j ≤ 2) :
    Covered q n (prefixWord n j false) := by
  have hp : 0 ≤ q := by linarith
  apply compressed_through hp (h := 2) (by omega) hj
  have hh := rowMass_mono_length hp 0 (show 4 ≤ n by omega)
  rw [geomTotal_rowMass]
  apply le_trans _ hh
  have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4/5) hq 2
  have h3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4/5) hq 3
  norm_num [rowMass,Finset.sum_range_succ] at *
  linarith

theorem child_zero {q : ℝ} (hq : 4/5 ≤ q) {n : ℕ} (hn : 4 ≤ n) :
    Covered q (n+1) (true :: prefixWord n 0 false) ∧
      Covered q (n+1) (false :: prefixWord n 0 false) := by
  constructor
  · rw [prefix_cons_true]
    exact prefix_two_covered hq (by omega) (by decide)
  · have e : false :: prefixWord n 0 false = prefixWord (n+1) 0 false := by
      simp [prefixWord,List.replicate_succ]
    rw [e]
    exact prefix_two_covered hq (by omega) (by decide)

theorem child_one {q : ℝ} (hq : 4/5 ≤ q) (hq1 : q ≤ 1) {n : ℕ} (hn : 4 ≤ n) :
    Covered q (n+1) (true :: prefixWord n 1 false) ∧
      Covered q (n+1) (false :: prefixWord n 1 false) := by
  constructor
  · rw [prefix_cons_true]
    exact prefix_two_covered hq (by omega) (by decide)
  · let k := n-2
    have e : n = (k+1)+1 := by dsimp [k]; omega
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hp : 0 ≤ q := by linarith
    have hsmall (i : ℕ) (hi : 2 ≤ i) : 1+q ≤ geomTotal q i := by
      rw [geomTotal_rowMass]
      apply le_trans _ (rowMass_mono_length hp 0 hi)
      simp [rowMass,Finset.sum_range_succ]
    have hT1 := hsmall k hk
    have hT2 := hsmall (k+1) (by omega)
    have ha : 1 ≤ q*(1+q) := by nlinarith [mul_nonneg (by linarith : 0 ≤ q-4/5) (by linarith : 0 ≤ q+4/5)]
    have hB : 1 ≤ (q*geomTotal q k)*(q*geomTotal q (k+1)) := by
      apply one_le_mul_of_one_le_of_one_le <;> exact ha.trans (mul_le_mul_of_nonneg_left (by assumption) hp)
    have hid := geomTotal_identity q k
    have hh := congrArg (fun x : ℝ => q^2*geomTotal q (k+1)*x) hid
    have hR := mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hB)
    have hnet : 1+q^n*geomTotal q (k+1) ≤ q*geomTotal q n := by
      rw [e,show geomTotal q (k+1+1) = 1+q*geomTotal q (k+1) from geomTotal_succ _ _]
      simp only [pow_succ] 
      nlinarith only [hR,hh]
    apply covered_chord (u := prefixWord (n+1) 0 false) (v := prefixWord (n+1) 1 false)
      (a := q) hp hq1
    · simp [geomMass,prefix_mass,rowMass,Finset.sum_range_succ]
    · rw [geomCut,prefix_one_cut]
      simp only [Bool.false_eq_true,if_false,prefixWord_length (by omega : 1 ≤ n),prefix_mass]
      have h0 : geomCut q (prefixWord (n+1) 0 false) = 0 := by simp [prefixWord,false_zero]
      rw [h0,e,prefix_one_cut]
      simp [rowMass] at *
      simpa only [e] using hnet
    · exact prefix_two_covered hq (by omega) (by decide)
    · exact prefix_two_covered hq (by omega) (by decide)
end GeometricMaxCut

namespace GeometricMaxCut

theorem covered_word_chord {q : ℝ} (hq : 0 < q) {n : ℕ} {u v w : List Bool}
    (h : WordChord q u w v) (hu : Covered q n u) (hv : Covered q n v) : Covered q n w := by
  obtain ⟨h1,h2,s,he,hs⟩ := h
  exact covered_slope_chord hq h1 h2 he hs hu hv

theorem reflect_prefix_bound {q : ℝ} {n i j : ℕ} (hj : j ≤ n)
    (h : geomMass q (prefixWord n i false) ≤ geomMass q (prefixWord n j true)) :
    rowMass q 0 i + rowMass q 0 j ≤ geomTotal q n := by
  rw [← prefixWord_compl,geomMass_compl,prefixWord_length hj,prefix_mass,prefix_mass] at h
  linarith

theorem inductive_children {q : ℝ} (ha : 4/5 ≤ q) (hq1 : q < 1) {h L : ℕ}
    (hh : 2 ≤ h) (hL : h ≤ L) (hm : 12 ≤ h+L+1) (he : Eligible q (h+L) h)
    (hole : WordChord q (prefixWord (h+L+1) (h-1) false) (false :: prefixWord (h+L) h false)
      (prefixWord (h+L+1) h false)) :
    Covered q (h+L+1) (true :: prefixWord (h+L) h false) ∧
      Covered q (h+L+1) (false :: prefixWord (h+L) h false) := by
  have hq : 0 < q := by linarith
  rw [prefix_cons_true]
  by_cases ee : h = L
  · subst L
    have central := central_word_chord hq hq1.le (h := h) (by omega) he
    have hb := reflect_prefix_bound (by omega : h+1 ≤ h+h+1) central.1
    have hsum : rowMass q 0 (h-1) + rowMass q 0 h ≤ geomTotal q (h+h+1) := by
      exact (add_le_add (le_refl _) (rowMass_mono_length hq.le 0 (by omega : h ≤ h+1))).trans hb
    have left := compressed_through hq.le (by omega : h ≤ (h+h+1)/2) (by omega : h-1 ≤ h) hsum
    have right := compressed_through hq.le (by omega : h ≤ (h+h+1)/2) (le_rfl : h ≤ h) hsum
    have rev := covered_word_chord hq central left right
    have inv := covered_reflect (prefixWord_length (by omega : h+1 ≤ h+h+1) true) rev
    have er : (prefixWord (h+h+1) (h+1) true).map Bool.not = prefixWord (h+h+1) (h+1) false := by
      simp [prefixWord,List.map_replicate]
    rw [er] at inv
    exact ⟨inv,covered_word_chord hq hole left right⟩
  · have hb := reflect_prefix_bound (by omega : h+1 ≤ h+L+1)
      (noncentral_word_mass ha hq1.le (by omega) (by omega) hm he)
    have span : rowMass q 0 (h+1-1) + rowMass q 0 (h+1) ≤ geomTotal q (h+L+1) := by simpa using hb
    have upper (j : ℕ) (hj : j ≤ h+1) := compressed_through hq.le (by omega : h+1 ≤ (h+L+1)/2) hj span
    exact ⟨upper _ le_rfl, covered_word_chord hq hole
      (upper _ (by omega)) (upper _ (by omega))⟩

theorem step_of_holes (holes : ∀ {q : ℝ} {h L : ℕ}, 4/5 ≤ q → q < 1 →
    2 ≤ h → h ≤ L → 12 ≤ h+L+1 → Eligible q (h+L) h →
    WordChord q (prefixWord (h+L+1) (h-1) false) (false :: prefixWord (h+L) h false)
      (prefixWord (h+L+1) h false))
    {n : ℕ} (hn : 11 ≤ n) {q : ℝ} (ha : 4/5 ≤ q) (hq : q < 1)
    (ih : HullAt q n) : HullAt q (n+1) := by
  apply child_diagram (by linarith) ih
  intro h he
  by_cases h0 : h = 0
  · subst h
    exact child_zero ha (by omega)
  by_cases h1 : h = 1
  · subst h
    exact child_one ha hq.le (by omega)
  have hb := he.1
  have hh : 2 ≤ h := by omega
  let L := n-h
  have hL : h ≤ L := by dsimp [L]; omega
  have e : h+L = n := by dsimp [L]; omega
  have hm : 12 ≤ h+L+1 := by omega
  have hel : Eligible q (h+L) h := e.symm ▸ he
  simpa only [e] using inductive_children ha hq hh hL hm hel (holes ha hq hh hL hm hel)

theorem induction_step {n : ℕ} (hn : 11 ≤ n) {q : ℝ} (ha : 4/5 ≤ q) (hq : q < 1)
    (ih : HullAt q n) : HullAt q (n+1) :=
  step_of_holes (fun hq hq1 hh hl hm he => block_word_chord hq hq1.le hh hl hm he) hn ha hq ih

end GeometricMaxCut

namespace GeometricMaxCut.FinitePoly

abbrev P := List ℚ

def val (x : ℝ) : P → ℝ
  | [] => 0
  | c :: p => c + x * val x p

def add : P → P → P
  | [], b => b
  | a, [] => a
  | a::p, b::r => (a+b)::add p r

def scale (a : ℚ) (p : P) : P := p.map (a * ·)

def mul : P → P → P
  | [], _ => []
  | a::p, r => add (scale a r) (0::mul p r)

def sub (p r : P) : P := add p (scale (-1) r)

def shift (a : ℚ) : P → P
  | [] => []
  | c::p =>
    let s := shift a p
    add [c] (add (scale a s) (0 :: s))

theorem val_add (x : ℝ) (p r : P) : val x (add p r) = val x p + val x r := by
  induction p generalizing r with
  | nil => simp [add, val]
  | cons c p ih =>
    cases r with
    | nil => simp [add, val]
    | cons b r => simp [add, val, ih]; ring

theorem val_scale (x : ℝ) (a : ℚ) (p : P) : val x (scale a p) = (a:ℝ) * val x p := by
  induction p with
  | nil => simp [scale, val]
  | cons c p ih =>
    change (a*c : ℚ) + x * val x (scale a p) = (a:ℝ) * ((c:ℝ) + x * val x p)
    rw [ih]
    push_cast
    ring

theorem val_mul (x : ℝ) (p r : P) : val x (mul p r) = val x p * val x r := by
  induction p with
  | nil => simp [mul,val]
  | cons c p ih => simp [mul,val_add,val_scale,val,ih]; ring

theorem val_sub (x : ℝ) (p r : P) : val x (sub p r) = val x p - val x r := by
  simp [sub, val_add, val_scale]; ring

theorem val_shift (x : ℝ) (a : ℚ) (p : P) : val x (shift a p) = val (x + a) p := by
  induction p with
  | nil => rfl
  | cons c p ih => simp only [shift,val_add,val_scale,val,ih]; push_cast; ring

def lower (w : ℚ) : P → ℚ
  | [] => 0
  | c::p => c + min 0 (w*lower w p)

theorem lower_sound (w : ℚ) {x : ℝ} (hx : 0 ≤ x) (hw : x ≤ (w:ℝ)) (p : P) :
    (lower w p : ℝ) ≤ val x p := by
  induction p with
  | nil => simp [lower,val]
  | cons c p ih =>
    simp only [lower, val, Rat.cast_add, Rat.cast_min, Rat.cast_zero, Rat.cast_mul]
    apply add_le_add_right
    have ht := mul_le_mul_of_nonneg_left ih hx
    by_cases h : 0 ≤ (lower w p : ℝ)
    · exact (min_le_left _ _).trans ((mul_nonneg hx h).trans ht)
    · exact (min_le_right _ _).trans ((mul_le_mul_of_nonpos_right hw (le_of_not_ge h)).trans ht)

def bound (a b : ℚ) (p : P) : ℚ := lower (b-a) (shift a p)

theorem bound_sound {x : ℝ} {a b : ℚ} (hx : (a:ℝ) ≤ x) (hy : x ≤ (b:ℝ)) (p : P) :
    (bound a b p : ℝ) ≤ val x p := by
  have h := lower_sound (b-a) (x := x-a) (by linarith) (by push_cast; linarith) (shift a p)
  simpa only [bound,val_shift,sub_add_cancel] using h

def zeroes (p : P) : Bool := p.all (· == 0)

theorem val_zeroes {p : P} (h : zeroes p = true) (x : ℝ) : val x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [zeroes, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [val,h.1,ih h.2]

theorem val_eq_of_eqv {p r : P} (h : zeroes (sub p r) = true) (x : ℝ) :
    val x p = val x r := by
  have := val_zeroes h x
  rw [val_sub] at this
  linarith

end GeometricMaxCut.FinitePoly


namespace GeometricMaxCut.FinitePoly
open GeometricMaxCut

theorem val_singleton (q : ℝ) (c : ℚ) : val q [c] = (c : ℝ) := by simp [val]

def massP : List Bool → P := List.map (fun b => if b then 1 else 0)

def cutP : List Bool → P
  | [] => []
  | b::w => add (if b then sub (massP (List.replicate w.length true)) (massP w) else massP w)
      (List.replicate w.length 0 ++ cutP w)

theorem val_mass (q : ℝ) (w : List Bool) : val q (massP w) = geomMass q w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp_all [massP,geomMass,val]

theorem val_prepend_zero (q : ℝ) (p : P) (n : ℕ) :
    val q (List.replicate n 0 ++ p) = q^n * val q p := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, val, ih, pow_succ]; ring

theorem val_cut (q : ℝ) (w : List Bool) : val q (cutP w) = geomCut q w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [cutP, val_add,val_prepend_zero,ih,val_sub,val_mass,geomCut,geomTotal]

def powP (p : P) : ℕ → P
  | 0 => [1]
  | n+1 => mul p (powP p n)

theorem val_powP (q : ℝ) (p : P) (n : ℕ) : val q (powP p n) = val q p ^ n := by
  induction n with
  | zero => simp [powP,val]
  | succ n ih => simp [powP,val_mul,ih,pow_succ, mul_comm]

def gapP (w l r : List Bool) : P :=
  add (mul (sub (cutP l) (cutP w)) (sub (massP r) (massP w)))
      (mul (sub (cutP r) (cutP w)) (sub (massP w) (massP l)))

def HasBound (q t : ℝ) (n : ℕ) (w : List Bool) : Prop :=
  ∃ k rev, Eligible q n k ∧ score q t w ≤ score q t (prefixWord n k rev)

theorem hasBound_self {q t : ℝ} {n h : ℕ} {rev : Bool} {w : List Bool}
    (hw : w = prefixWord n h rev) (he : Eligible q n h) : HasBound q t n w := by
  exact ⟨h,rev,he,hw ▸ le_rfl⟩

theorem hasBound_chord {q t : ℝ} {n i j : ℕ} {b c : Bool} {w : List Bool}
    (he : Eligible q n i) (hf : Eligible q n j)
    (h1 : 0 ≤ val q (sub (massP w) (massP (prefixWord n i b))))
    (h2 : 0 ≤ val q (sub (massP (prefixWord n j c)) (massP w)))
    (h3 : 0 < val q (sub (massP (prefixWord n j c)) (massP (prefixWord n i b))))
    (h4 : 0 ≤ val q (gapP w (prefixWord n i b) (prefixWord n j c))) : HasBound q t n w := by
  simp only [gapP,val_add,val_mul,val_sub,val_mass,val_cut] at h1 h2 h3 h4
  by_cases hl : score q t w ≤ score q t (prefixWord n i b)
  · exact ⟨i,b,he,hl⟩
  · refine ⟨j,c,hf,?_⟩
    by_contra! hr
    simp only [score, not_le] at hr hl
    rcases eq_or_lt_of_le h1 with e | e
    · have haux := mul_neg_of_neg_of_pos (sub_neg.mpr hl) (show 0 < geomMass q (prefixWord n j c)-geomMass q w by linarith)
      have hz := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr.le) h1
      nlinarith
    · have haux := mul_neg_of_neg_of_pos (sub_neg.mpr hr) e
      have haux2 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl.le) h2
      nlinarith

theorem eligible_piece {q : ℝ} {n j k : ℕ}
    (h : 0 ≤ val q (sub (cutP (prefixWord n k false)) (cutP (prefixWord n j false)))) :
    geomCut q (prefixWord n j false) ≤ geomCut q (prefixWord n k false) := by
  simpa [val_sub,val_cut] using h

theorem bound_negative {q : ℝ} {a b : ℚ} {p : P} (ha : (a:ℝ) ≤ q) (hb : q ≤ (b:ℝ))
    (cert : 0 < bound a b (scale (-1) p)) : val q p < 0 := by
  have h := bound_sound ha hb (scale (-1) p)
  rw [val_scale] at h
  have pos : (0:ℝ) < (bound a b (scale (-1) p) : ℝ) := by exact_mod_cast cert
  push_cast at h
  linarith

theorem bound_positive {q : ℝ} {a b : ℚ} {p : P} (ha : (a:ℝ) ≤ q) (hb : q ≤ (b:ℝ))
    (cert : 0 < bound a b p) : 0 < val q p := by
  exact lt_of_lt_of_le (by exact_mod_cast cert) (bound_sound ha hb p)

end GeometricMaxCut.FinitePoly

namespace GeometricMaxCut.FinitePoly
open GeometricMaxCut

theorem hasBound_compl {q t : ℝ} {n : ℕ} {w : List Bool} (hw : w.length = n)
    (h : HasBound q (-t) n (w.map Bool.not)) : HasBound q t n w := by
  obtain ⟨k,r,hk,hs⟩ := h
  have hlen := prefixWord_length (n:=n) (h:=k) (by have := hk.1; omega) false
  refine ⟨k, !r, hk, ?_⟩
  cases r <;> simp only [Bool.not_false, Bool.not_true, score] at hs ⊢
  · rw [← prefixWord_compl, geomCut_compl, geomMass_compl, hlen]
    rw [geomCut_compl, geomMass_compl, hw] at hs
    linarith
  · simp only [← prefixWord_compl, geomCut_compl, geomMass_compl, hlen, hw] at hs
    linarith

theorem seven_word {w : List Bool} (h : w.length = 7) :
    ∃ a b c d e f g : Bool, w = [a,b,c,d,e,f,g] := by
  rcases w with _ | ⟨a,w⟩ <;> simp at h
  rcases w with _ | ⟨b,w⟩ <;> simp at h
  rcases w with _ | ⟨c,w⟩ <;> simp at h
  rcases w with _ | ⟨d,w⟩ <;> simp at h
  rcases w with _ | ⟨e,w⟩ <;> simp at h
  rcases w with _ | ⟨f,w⟩ <;> simp at h
  rcases w with _ | ⟨g,w⟩ <;> simp at h
  subst w
  exact ⟨_,_,_,_,_,_,_,rfl⟩

end GeometricMaxCut.FinitePoly


namespace GeometricMaxCut.FinitePoly.Certificate
open GeometricMaxCut

abbrev Table := Array P
abbrev Assumption := Option (ℕ × Ordering)

def Holds (q : ℝ) (tab : Table) : Assumption → Prop
  | none => True
  | some (i,.lt) => val q tab[i]! < 0
  | some (i,.eq) => val q tab[i]! = 0
  | some (i,.gt) => 0 < val q tab[i]!

abbrev Power := ℕ × Bool × ℕ

def signed (tab : Table) (i : ℕ) (neg : Bool) : P :=
  if neg then scale (-1) tab[i]! else tab[i]!

def productP (tab : Table) (c : ℕ) : List Power → P
  | [] => [c]
  | (i,b,e)::es => mul (powP (signed tab i b) e) (productP tab c es)

def signCheck (tab : Table) (a b : ℚ) (h : Assumption) (i : ℕ) (neg : Bool) : Bool :=
  h == some (i,if neg then Ordering.lt else Ordering.gt) ||
  (!neg && tab[i]! == [0,1]) || (neg && tab[i]! == [-1,1]) ||
  decide (0 < bound a b (signed tab i neg))

theorem signCheck_sound {tab : Table} {a b : ℚ} {h : Assumption} {i : ℕ} {neg : Bool}
    {q : ℝ} (ha : (a:ℝ) ≤ q) (hb : q ≤ (b:ℝ)) (hq0 : 0 < q) (hq1 : q < 1)
    (hh : Holds q tab h) (ok : signCheck tab a b h i neg = true) : 0 < val q (signed tab i neg) := by
  unfold signCheck at ok
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  rcases ok with ((H | H) | H) | H
  · cases neg <;> simp_all [signed,Holds,val_scale]
  · rcases H with ⟨H,heq⟩
    cases neg <;> simp_all [signed, val]
  · rcases H with ⟨hn,heq⟩
    cases neg <;> simp_all [signed, val_scale,val]
  · exact bound_positive ha hb H

theorem productP_positive {tab : Table} {a b : ℚ} {h : Assumption} {c : ℕ}
    {q : ℝ} (ha : (a:ℝ) ≤ q) (hb : q ≤ (b:ℝ)) (hq0 : 0 < q) (hq1 : q < 1)
    (hh : Holds q tab h) (hc : 0 < c) (es : List Power)
    (ok : es.all (fun e => signCheck tab a b h e.1 e.2.1) = true) :
    0 < val q (productP tab c es) := by
  induction es with
  | nil => simpa [productP,val] using (show (0:ℝ) < c by exact_mod_cast hc)
  | cons e es ih =>
    rcases e with ⟨i,n,k⟩
    have H := Bool.and_eq_true_iff.mp ok
    rw [productP,val_mul,val_powP]
    exact mul_pos (pow_pos (signCheck_sound ha hb hq0 hq1 hh H.1) _) (ih H.2)

inductive Hint where
  | positive (c : ℕ) (es : List Power)
  | zero
  | root (i quotient : ℕ)
  deriving Inhabited

abbrev Requirement := P × Bool
def Satisfies (q : ℝ) (r : Requirement) : Prop :=
  if r.2 then 0 < val q r.1 else 0 ≤ val q r.1

def verify (tab : Table) (a b : ℚ) (h : Assumption) (r : Requirement) : Hint → Bool
  | .positive c es =>
    decide (0 < c) && zeroes (sub r.1 (productP tab c es)) &&
    es.all (fun e => signCheck tab a b h e.1 e.2.1)
  | .zero => !r.2 && zeroes r.1
  | .root i quotient =>
    !r.2 && h == some (i,Ordering.eq) && zeroes (sub r.1 (mul tab[i]! tab[quotient]!))

theorem verify_sound {tab : Table} {a b : ℚ} {h : Assumption} {q : ℝ}
    (ha : (a:ℝ) ≤ q) (hb : q ≤ (b:ℝ)) (hq0 : 0 < q) (hq1 : q < 1) (hh : Holds q tab h)
    {r : Requirement} {hint : Hint} (ok : verify tab a b h r hint = true) : Satisfies q r := by
  cases hint with
  | positive c es =>
    simp only [verify,Bool.and_eq_true,decide_eq_true_eq] at ok
    have e := val_eq_of_eqv ok.1.2 q
    have H := productP_positive ha hb hq0 hq1 hh ok.1.1 es ok.2
    unfold Satisfies
    rw [e]
    split <;> first | exact H | exact H.le
  | zero =>
    simp only [verify, Bool.and_eq_true,Bool.not_eq_true'] at ok
    simp [Satisfies,ok.1, val_zeroes ok.2 q]
  | root i j =>
    simp only [verify,Bool.and_eq_true, Bool.not_eq_true',beq_iff_eq] at ok
    have H := val_eq_of_eqv ok.2 q
    rw [ok.1.2] at hh
    simpa [Satisfies,ok.1.1,H,val_mul,show val q tab[i]! = 0 from hh]

def checks (tab : Table) (hints : Array Hint) (a b : ℚ) (h : Assumption) :
    List Requirement → List ℕ → Bool
  | [], [] => true
  | r::rs, i::ids => verify tab a b h r hints[i]! && checks tab hints a b h rs ids
  | _, _ => false

theorem checks_sound {tab : Table} {hints : Array Hint} {a b : ℚ} {h : Assumption} {q : ℝ}
    (ha : (a:ℝ) ≤ q) (hb : q ≤ (b:ℝ)) (hq0 : 0 < q) (hq1 : q < 1) (hh : Holds q tab h)
    {rs : List Requirement} {ids : List ℕ} (ok : checks tab hints a b h rs ids = true) :
    ∀ r ∈ rs, Satisfies q r := by
  induction rs generalizing ids with
  | nil => simp
  | cons r rs ih =>
    cases ids with
    | nil => simp [checks] at ok
    | cons id ids =>
      have H := Bool.and_eq_true_iff.mp ok
      intro s hs
      rcases List.mem_cons.mp hs with rfl|hs
      · exact verify_sound ha hb hq0 hq1 hh H.1
      · exact ih H.2 _ hs

def eligibleReq (n k : ℕ) : List Requirement :=
  (List.range k).map fun i => (sub (cutP (prefixWord n k false)) (cutP (prefixWord n i false)),false)

theorem eligibleReq_sound {n k : ℕ} {q : ℝ} (hk : k ≤ n/2)
    (H : ∀ r ∈ eligibleReq n k, Satisfies q r) : Eligible q n k := by
  refine ⟨hk,?_⟩
  intro i hi
  rcases eq_or_lt_of_le hi with rfl|h
  · exact le_rfl
  · exact eligible_piece (H _ (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩))

def endpoint (n e : ℕ) := prefixWord n (e/2) (e%2 == 1)

def chordReq (w l r : List Bool) : List Requirement :=
  [(sub (massP w) (massP l),false), (sub (massP r) (massP w),false),
   (sub (massP r) (massP l),true), (gapP w l r,false)]

def requirements (n : ℕ) (w : List Bool) (i j : ℕ) : List Requirement :=
  if i=j then eligibleReq n (i/2)
  else eligibleReq n (i/2) ++ eligibleReq n (j/2) ++ chordReq w (endpoint n i) (endpoint n j)

def leafCheck (tab : Table) (hints : Array Hint) (a b : ℚ) (h : Assumption)
    (n : ℕ) (w : List Bool) (i j : ℕ) (ids : List ℕ) : Bool :=
  decide (i/2 ≤ n/2 ∧ j/2 ≤ n/2) && (i != j || w == endpoint n i) &&
  checks tab hints a b h (requirements n w i j) ids

theorem leafCheck_sound {tab : Table} {hints : Array Hint} {a b : ℚ} {h : Assumption} {q : ℝ}
    (ha : (a:ℝ) ≤ q) (hb : q ≤ (b:ℝ)) (hq0 : 0 < q) (hq1 : q < 1) (hh : Holds q tab h)
    {n i j : ℕ} {w : List Bool} {ids : List ℕ} (t : ℝ)
    (ok : leafCheck tab hints a b h n w i j ids = true) : HasBound q t n w := by
  simp only [leafCheck,Bool.and_eq_true,decide_eq_true_eq,
    Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at ok
  have H := checks_sound ha hb hq0 hq1 hh ok.2
  by_cases heq : i=j
  · subst j
    simp only [requirements,if_pos rfl] at H
    exact hasBound_self (ok.1.2.resolve_left (not_not_intro rfl)) (eligibleReq_sound ok.1.1.1 H)
  · simp only [requirements,if_neg heq, List.mem_append] at H
    apply hasBound_chord (b:=i%2==1) (c:=j%2==1)
      (eligibleReq_sound ok.1.1.1 (fun r hr => H r (Or.inl (Or.inl hr))))
      (eligibleReq_sound ok.1.1.2 (fun r hr => H r (Or.inl (Or.inr hr))))
    · exact H (sub (massP w) (massP (endpoint n i)), false) (Or.inr (by simp [chordReq,endpoint]))
    · exact H (sub (massP (endpoint n j)) (massP w), false) (Or.inr (by simp [chordReq,endpoint]))
    · exact H (sub (massP (endpoint n j)) (massP (endpoint n i)), true) (Or.inr (by simp [chordReq,endpoint]))
    · exact H (gapP w (endpoint n i) (endpoint n j), false) (Or.inr (by simp [chordReq,endpoint]))

inductive Tree where
  | leaf (i j : ℕ) (ids : List ℕ)
  | bisect (left right : Tree)
  | signs (i : ℕ) (neg zero pos : Tree)
  deriving Inhabited

def treeCheck (tab : Table) (hints : Array Hint) (n : ℕ) (w : List Bool) :
    ℚ → ℚ → Assumption → Tree → Bool
  | a,b,h,.leaf i j ids => leafCheck tab hints a b h n w i j ids
  | a,b,h,.bisect l r => treeCheck tab hints n w a ((a+b)/2) h l &&
      treeCheck tab hints n w ((a+b)/2) b h r
  | a,b,_,.signs i l m r => treeCheck tab hints n w a b (some (i,.lt)) l &&
      treeCheck tab hints n w a b (some (i,.eq)) m && treeCheck tab hints n w a b (some (i,.gt)) r

theorem treeCheck_sound {tab : Table} {hints : Array Hint} {n : ℕ} {w : List Bool} {q : ℝ}
    {a b : ℚ} {h : Assumption} (ha : (a:ℝ) ≤ q) (hb : q ≤ (b:ℝ))
    (hq0 : 0 < q) (hq1 : q < 1) (hh : Holds q tab h) (t : ℝ)
    (tr : Tree) (ok : treeCheck tab hints n w a b h tr = true) : HasBound q t n w := by
  induction tr generalizing a b h with
  | leaf i j ids => exact leafCheck_sound ha hb hq0 hq1 hh t ok
  | bisect l r ihl ihr =>
    have H := Bool.and_eq_true_iff.mp ok
    rcases le_total q ((((a+b)/2:ℚ)):ℝ) with hl|hr
    · exact ihl ha hl hh H.1
    · exact ihr hr hb hh H.2
  | signs i l m r ihl ihm ihr =>
    have H := Bool.and_eq_true_iff.mp ok
    have H' := Bool.and_eq_true_iff.mp H.1
    rcases lt_trichotomy (val q tab[i]!) 0 with hneg|hzero|hpos
    · exact ihl (h := some (i,Ordering.lt)) ha hb hneg H'.1
    · exact ihm (h := some (i,Ordering.eq)) ha hb hzero H'.2
    · exact ihr (h := some (i,Ordering.gt)) ha hb hpos H.2

theorem initial_sound {tab : Table} {hints : Array Hint} {n : ℕ} {w : List Bool} {q t : ℝ}
    (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) (tr : Tree)
    (ok : treeCheck tab hints n w (4/5) 1 none tr = true) : HasBound q t n w :=
  treeCheck_sound (tab:=tab) (n:=n) (w:=w) (h:=none) (b:=(1:ℚ)) ha (by simpa using hq.le) (lt_of_lt_of_le (by norm_num) ha) hq trivial t tr ok

end GeometricMaxCut.FinitePoly.Certificate


namespace GeometricMaxCut.FinitePoly.F7
open GeometricMaxCut FinitePoly Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def coefficients : Table := #[
  [1,1],
  [1,-1,1],
  [1,1,1],
  [0,1],
  [-1,1],
  [-1,0,1,2,3,4,4,3,2,1],
  [-1,1,-1,1,-1,1,0,1,0,1],
  [-1,1,0,1,0,1],
  [-1,1,1,1,1,1,1],
  [1,1,1,1,1],
  [1,-1,1,-1,1],
  [-1,2,-1,1,1,0,1,1,0,1],
  [-1,1,0,1,1,1,1],
  [-1,0,0,0,0,1,0,0,0,0,1,1,1,1],
  [-1,0,1,2,3,3,2,1],
  [1,0,1],
  [-1,1,0,0,-1,0,1,1],
  [-1,1,1],
  [-1,0,0,0,0,1,0,0,0,1],
  [-1,0,1,0,1,-1,1,0,1],
  [-1,1,0,0,1],
  [-1,-1,0,0,0,1,1,1,1,1],
  [-1,0,0,1,0,1],
  [1,0,-1,0,-1,0,-1,-1,0,-1,1,-1,3,-1,3,0,2,0,1],
  [-1,0,0,1,0,-1,-1,0,1,1,1],
  [-1,0,1,1],
  [1,1,0,1],
  [1,0,0,0,0,1,0,0,0,1],
  [0,1,0,0,1],
  [-1,0,1,2,3,3,4,4,4,3,3,3,3,2,1],
  [-1,1,1,1],
  [-1,0,0,0,0,1,0,0,0,1,0,0,0,1,1,1],
  [-1,0,1,2,2,3,3,3,2,1],
  [-1,-1,-1,-1,-1,-1,0,0,1,2,3,2,3,3,3,2,1],
  [-1,1,0,1],
  [1,0,1,1,1],
  [-1,0,-1,-1,-1,1,0,1,1,1,1,0,0,0,1,1,1],
  [-1,-1,0,0,1,1,1,1,2,1,1,1,2,2,1],
  [-1,0,1,0,1,1,1],
  [-1,1,0,-1,1,0,0,0,0,1,0,-1,0,1],
  [-1,-1,1,0,1,1,1],
  [1,0,-1,0,-1,0,-2,1,-1,0,-1,2,2,0,0,0,1,0,1,1,1],
  [-1,0,0,0,0,-1,0,0,0,1,0,0,0,1,1,1],
  [-1,0,0,0,-1,0,1,2,1],
  [-1,-1,-1,-1,-1,-2,-2,-1,-1,-1,-1,0,2,5,6,5,3,1],
  [1,1,0,0,1,1,1],
  [-1,-1,1,1,-1,-1,-1,1,1,0,0,0,0,1,1,1,1,1,1],
  [-1,-1,0,0,1,0,1,1,2,2,3,2,2,1,1],
  [-1,1,0,0,1,1,1],
  [-1,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1],
  [-1,1,-1,1,0,1],
  [1,0,-1,0,-1,-1,0,0,0,0,0,-1,1,-1,2,-1,3,0,2,0,1],
  [1,-2,1,-1,1,-1,1,-1,0,-1,0,0,1,0,1,0,1],
  [1,0,1,1],
  [-1,-1,-1,-1,-1,-1,-2,-1,-2,0,1,3,3,4,3,3,2,1],
  [-1,0,0,0,0,1,0,0,0,1,0,0,1],
  [-1,2,-1,3,-2,2,-3,0,-5,-1,-3,1,-1,2,1,2,1,2,3,2,2,1,1],
  [1,0,0,-1,-1,-1,-1,-1,0,0,0,0,1,1,1,1,1,1],
  [-1,-2,-3,-2,-1,0,1,1,1,1,1,2,2,2,2,2,1],
  [1,-2,1,-2,1,-1,0,0,0,1,-1,1],
  [-1,-1],
  [-1,1,-1,1,-1,1,-1,1,0,0,0,0,1,-1,1],
  [-1,-1,0,0,1,1,1],
  [1,0,-1,0,-1,1,-1,0,-1,1,-1,0,1],
  [-1],
  [1,0,-1,0,-1,0,-1,0,-2,1,-1,1,-1,2,0,0,1,1,1,0,1],
  [-1,0,-2,0,-1,-1,0,-3,1,-3,3,-2,4,0,3,0,1],
  [-1,1,0,2,1,2,2,2,2,1,2,1,1,1,1],
  [-1,1,1,1,0,1,1],
  [-1,0,0,0,0,1,0,0,0,1,0,0,1,0,0,1,1],
  [-1,0,1,2,2,3,3,2,2,2,1],
  [-1,0,0,-1,0,1,0,0,1,0,0,1,-1,1,0,0,0,1],
  [-1,0,0,-1,1,0,1,0,2,0,2,1,1,2,1,1,1,1],
  [-1,0,1,1,0,1,1],
  [-1,1,-1,0,0,0,1,0,0,1,0,0,1,-1,1,0,0,0,1],
  [1,-2,1,-2,1,-1,0,0,0,-1,1,0,0,1,1,0,0,2,1,1,1,1],
  [-1,0,1,0,0,1],
  [-1,1,-1,1,-1,0,0,0,0,1,-1,1,0,0,0,1],
  [-1,0,-1,0,-1,1,-1,2,0,1,1,1],
  [-1,0,1,0,1],
  [1,1,0,1,0,1,1],
  [-1,-1,1,-1,1,-1,-1,1,0,1,0,0,1,0,1,1,1,0,0,1,1],
  [1,2,1,1],
  [-1,-1,-1,-1,1,0,2,1,3,3,4,4,4,3,2,2,2,1],
  [-1,0,-1,0,0,1,0,1,0,0,1,0,1,1,1,0,0,1,1],
  [-1,0,0,1,0,1,1],
  [1,0,0,0,-2,-1,-1,-1,0,0,-1,1,-1,1,0,3,1,1,1,2,1,1,1,1],
  [1,-1,0,-1,0,0,0,-1,0,-1,-1,1,0,1,1,1,0,0,1,1],
  [-1,-1,-1,-1,1,0,2,1,2,1,2,2,1],
  [-1,2,-1,1],
  [-1,0,-1,-1,0,1,0,1,1,1,0,1,1,1,0,0,1,1],
  [-1,2,0,0,1,-1,0,-4,0,-3,-1,-2,3,-1,2,1,3,1,1,1,2,1,1,1,1],
  [1,0,-1,0,-1,-1,-1,0,-1,0,0,1,0,1,1,1,0,0,1,1],
  [1,0,-1,0,-1,0,1,0,0,0,0,0,0,1,1,2,1,2,2,1],
  [-1,-1,0,-1,0,0,0,1,0,1,1,1,0,1,1,1,0,0,1,1],
  [-1,-1,0,1,0,1,1],
  [1,0,0,1,-2,0,-2,0,-1,0,-2,0,0,0,0,0,1,1],
  [1,1,-1,0,-1,-2,-1,-3,0,-3,0,-2,3,-1,2,1,3,1,1,1,2,1,1,1,1],
  [1,2,3,2,2,1],
  [1,2,3,2,3,3,3,4,3,4,2,-1,-4,-5,-6,-5,-3,-1,1,1],
  [-1,0,0,1,1],
  [1,-1,-1,-1,-1,0,-1,0,0,1,0,0,0,0,1,0,1],
  [1,1,1,0,0,1,1],
  [-1,-1,-1,1,1,-1,-1,0,1,1,0,0,1,1,0,0,0,1,1,1,1],
  [-1,-1,0,0,1,0,1,1,2,1,2,2,2,2,1,1],
  [-1,1,1,0,0,1,1],
  [-1,0,0,0,0,1,0,0,0,1,0,0,0,0,1,0,1],
  [1,0,-1,0,-1,-1,0,0,0,-1,1,0,1,0,0,1,-1,2,0,2,0,1],
  [-1,2,0,1,-2,1,-1,-2,-2,1,0,-2,0,1,0,0,0,1,0,1,2,2,2,1,1],
  [1,-1,0,-1,1,-1,0,0,0,-1,0,1,0,0,0,0,1,0,1],
  [-1,-1,0,0,0,0,1,1,2,1,1],
  [1,0,0,1,1],
  [-1,0,0,-1,-1,1,0,0,1,1,1,1,0,0,0,1,1,1,1],
  [1,0,1,0,0,1,1],
  [-1,1,-1,1,1,-2,-1,0,0,0,0,0,1,1,0,0,0,1,1,1,1],
  [-1,1,0,0,1,1],
  [1,-1,0,0,-1,-1,0,-1,-1,0,0,1,1,0,0,0,1,1,1,1],
  [1,1,2,1],
  [1,0,1,0,-1,0,1,-1,0,-1,0,-1,0,-1,1,2,3,3,2,1],
  [-1,1,-2,1,-1,1,0,0,0,1,0,1,0,0,0,0,1,0,1],
  [-1,-1,1,0,0,1,1],
  [1,0,0,1,-2,-1,-3,0,-2,-1,-2,0,0,1,2,2,0,1,0,1,2,2,2,1,1],
  [-1,-2,-2,-4,-5,-6,-6,-5,-5,-4,-3,-1,0,2,2,2,1,1],
  [1,-1,0,1],
  [-1,1,-1,1,-2,1,0,1,0,0,0,0,0,1,0,0,1,0,1],
  [-1,-1,1,1,1],
  [-1,0,1,0,1,-3,1,0,1,0,-1,0,0,0,1,0,0,1,0,1],
  [-1,0,0,0,0,-1,0,0,0,1,0,0,1,0,1],
  [1,1,0,0,-1,1,0,-1,-1,-2,0,-1,1,0,1,1,2,1,1],
  [-1,1,0,0,0,1,1],
  [-1,-1,0,1,0,0,1,1,-1,-1,1,1,0,0,0,1,1],
  [-1,3,-2,2,-4,2,-4,0,-2,3,0,1,0,-1,-1,0,0,1,1,2,2,2,2,1,1],
  [-1,0,0,0,0,1,1],
  [1,-1,-1,-1,0,0,0,0,0,-1,-1,0,0,1,1,0,1,1,1,1],
  [1,0,1,2,3,2,1,-1,-1,-3,-2,-3,-1,-1,0,0,1,1,1,1],
  [-1,1,1,1,1],
  [-1,0,0,0,0,1,0,0,0,1,0,0,1,0,1],
  [-1,0,0,0,1,1],
  [1,0,0,0,0,1,1],
  [1,0,1,0,0,-1,-1,-2,-1,-1,0,-1,-1,0,0,-1,1,1,1,1],
  [-1,0,-1,0,1,0,0,0,1,0,0,1,0,1],
  [1,-1,1,-1,0,-1,0,-1,0,0,0,0,0,1,0,0,1,0,1],
  [1,1,2,2,1,0,0,-1,-2,-1,0,0,1],
  [1,-1,-1,-1,-1,0,-1,0,0,1,0,0,1,0,1],
  [1],
  [-1,-1,-1,-1,-1,1,1,0,0,0,1,1,0,0,1,1,0,1,1,1,1],
  [-1,-1,0,0,1,0,1,1,2,1,2,2,1,1],
  [-1,0,1,2,3,3,4,4,4,3,3,3,2,2,1,1],
  [-1,2,-1,2,-1,1],
  [1,-1,1,-1,1,-1,1],
  [-1,0,0,0,0,1,0,1,0,1],
  [-1,1,0,2,0,3,0,2,0,1],
  [1,1,1,0,1],
  [-1,-1,-1,0,-1,1,1,1,0,1,0,0,1,0,0,1,0,1,0,1],
  [1,0,0,0,1],
  [-1,-1,0,0,0,0,1,0,1,1,2,2,3,2,3,3,2,2,1,1],
  [-1,1,1,-1,1],
  [-1,0,0,0,-1,0,1,1,1,0,1,0,0,1,0,0,1,0,1,0,1],
  [1,-3,4,-6,7,-8,8,-8,8,-9,10,-10,10,-9,9,-7,6,-3,3,-1,1],
  [-1,-1,1,1,1,0,1],
  [-1,0,1,0,-1,-1,1,1,-1,0,1,0,0,0,1],
  [-1,0,1,1,2,1,1],
  [1,-1,-1,0,-2,-1,-2,-1,0,-1,1,1,0,1,0,1,0,1,0,1],
  [1,1,0,1,1,0,1],
  [-1,-1,1,-1,-1,1,-1,1,0,0,1,0,1,1,0,1,0,1,0,1,0,1],
  [-1,-1,0,-1,0,0,1,2,2,3,3,3,3,3,3,2,2,1,1],
  [-1,1,0,1,1,0,1],
  [-1,0,0,-1,0,1,0,0,1,0,1,1,0,1,0,1,0,1,0,1],
  [-1,1,-1,2,-1,1],
  [1,0,-1,1,-1,-2,0,-1,-1,0,-1,0,1,0,2,0,3,-1,3,-1,3,0,2,0,1],
  [1,-1,0,0,-1,0,0,-1,-1,0,-1,1,1,0,1,0,1,0,1,0,1],
  [-1,-1,1,0,-1,0,1,1,0,1,1,1],
  [-1,1,1,0,0,1],
  [-1,-1,0,-1,0,1,1,0,1,1,1,0,1,0,1,0,1,0,1],
  [1,0,0,1,1,0,1],
  [-1,1,1,-1,-1,0,-1,0,0,0,0,0,1,1,0,1,0,1,0,1,0,1],
  [-1,0,1,1,0,1],
  [1,0,-1,-1,-1,-1,0,1,1,0,0,0,0,0,1,0,1],
  [1,0,-1,0,1,0,1,0,0,-1,0,-1,0,-1,1,1,2,1,2,1,1],
  [1,1,0,0,1],
  [-1,-1,0,0,-1,0,0,1,1,0,1,1,1,0,1,0,1,0,1,0,1],
  [-1,-1,0,1,1,0,1],
  [-1,0,0,-1,0,-1,0,0,-1,0,1,1,0,1,0,1,0,1,0,1],
  [1,1,2,0,1],
  [1,2,3,2,1,3,3,4,3,2,2,-1,-4,-6,-5,-4,-1,0,1,1,1],
  [1,-1,-1,-1,-1,0,-1,0,0,1,0,0,0,1,0,0,1],
  [1,1,1,0,1,0,1],
  [-1,-1,-1,1,-1,1,-1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1],
  [1,2,2,1,1],
  [-1,-1,0,0,1,0,1,1,2,1,2,2,2,1,1,1],
  [-1,1,1,0,1,0,1],
  [-1,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,1],
  [-1,0,1,0,1,0,1],
  [1,0,-1,0,-1,-1,0,0,0,-1,1,0,1,-1,2,0,0,1,1,1,0,1],
  [-1,2,0,0,1,-2,2,-5,2,-4,2,-4,3,-3,3,-2,3,-1,2,1,1,2,1,2,0,1],
  [-1,-1,0,0,1,0,0,0,0,0,1,0,1],
  [-1,0,1,-1,0,1,0,0,1],
  [-1,0,-1,0,-1,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1],
  [-1,1,0,0,-1,0,1,-1,0,0,1,0,0,1],
  [1,0,-1,0,1],
  [1,-1,0,-1,0,-1,0,-1,0,-1,0,1,0,1,0,1,0,1,1,0,1],
  [1,0,0,0,1,0,0,-1,0,-1,0,-1,0,0,1,1,1,1,1],
  [1,1,0,1,0,1],
  [-1,-1,1,-1,1,-1,1,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1],
  [1,-2,1,-2,1,-1,0,0,0,-1,1,0,1,-1,2,0,0,1,1,1,0,1],
  [-1,-1,1,0,1,0,1],
  [-1,0,0,0,0,-1,0,0,0,1,0,0,0,1,0,0,1],
  [1,2,1,2,1,2,1,-1,-1,-2,-2,-2,-3,-1,-2,1,0,2,1,1,1],
  [1,0,0,1,0,1],
  [-1,0,0,-1,0,-1,1,1,0,1,0,0,1,0,1,1,0,1,1,0,1],
  [1,-2,0,0,1,-1,-1,1,1,-2,0,2,0,-1,1,1,0,0,1],
  [-1,-1,1,1,0,1],
  [-1,0,0,0,0,-1,0,0,0,1,0,0,1,0,0,1],
  [1,2,1,0,1,0,1,-1,-2,-2,-2,-2,0,-1,1,1,2,2,2,1,1],
  [-1,0,0,-1,1,0,1,-1,2,-2,2,-1,1,0,1,-1,2,-1,1],
  [-1,4,-6,7,-8,7,-8,5,-3,1,1,-2,3,-4,4,-4,5,-4,5,-3,4,-2,3,-1,1],
  [-1,0,0,0,1,0,1],
  [1,-2,1,-1,0,0,0,0,-1,1,-2,2,-1,1,0,1,-1,2,-1,1],
  [1,-1,1,1,0,0,0,-1,0,-1,0,-1,1,-1,1,0,0,1],
  [-1,1,1,1,0,1],
  [-1,0,0,0,0,1,0,0,0,1,0,0,1,0,0,1],
  [-1,-1,-1,1,-1,1,0,1,0,1,1,0,1,1,0,1],
  [1,0,0,-1,0,-1,-1,-1,0,-1,0,0,1,0,1,1,0,1,1,0,1],
  [-1,-1,0,0,0,0,1,0,1,1],
  [1,-1,-1,-1,-1,0,-1,0,0,1,0,0,1,0,0,1],
  [1,1,1,1,0,1],
  [-1,-1,-1,-1,1,-1,1,0,0,1,0,1,0,1,0,1,1,0,1,1,0,1],
  [-1,-1,0,0,1,0,1,1,2,1,2,2,1,1,1],
  [1,-1,-1,-1,-1,0,-1,0,0,1,0,0,1,0,0,0,1],
  [1,1,1,1,0,0,1],
  [-1,-1,-1,-1,1,1,-1,0,0,1,1,0,0,1,1,0,1,1,0,0,1,1],
  [-1,-1,0,0,1,0,1,1,2,1,2,2,1,1,1,1],
  [-1,2,0,-1,1],
  [-1,1,0,-1,1,1,-2,1,1,-1,0,1,0,-1,1],
  [-1,1,0,1,-1,1],
  [1,0,-1,0,-1,-1,0,0,0,-1,1,0,0,1,1,1,-1,2,0,1,0,1],
  [1,-1,1,-2,1,-1,0,-1,1,-1,0,0,1,0,0,1,0,0,0,1],
  [-1,-1,0,0,-1,1,1,0,0,1,0,1,1,0,1,1,0,0,1,1],
  [-1,3,-2,1,-2,2,-4,0,-1,2,-3,1,-1,0,0,1,1,2,2,0,1,2,1,1,1,1],
  [1,-1,-1,0,0,-1,0,0,-1,-1,0,0,1,1,0,1,1,0,0,1,1],
  [1,1,2,2,1],
  [1,0,1,2,1,0,1,-1,-1,-2,-1,-2,0,-1,0,1,1,1,2,2,1],
  [-1,1,-1,0,-1,1,0,1,-1,1,0,0,1,0,0,1,0,0,0,1],
  [1,-2,1,-2,1,-1,0,0,0,-1,1,0,0,1,1,1,-1,2,0,1,0,1],
  [-1,-1,1,1,0,0,1],
  [-1,0,0,0,0,-1,0,0,0,1,0,0,1,0,0,0,1],
  [1,1,0,0,1,1,0,-1,-1,-1,0,-2,1,-2,1,0,1,0,1,1],
  [1,0,1,0,0,1],
  [-1,2,-3,3,-2,0,2,-2,1,1,-2,2,-1,0,1,0,-1,1],
  [1,-3,4,-5,4,-4,2,-1,0,-1,2,-2,2,-2,3,-1,2,-1,2,0,1,0,1],
  [-1,-1,1,0,1,1],
  [-1,0,0,-1,0,0,0,0,0,1,0,0,1,1],
  [1,1,0,2,-1,1,0,-1,0,-2,-1,-1,-1,0,0,1,0,1,1,1],
  [-1,1,0,1,0,0,1],
  [-1,0,-1,-1,0,1,0,1,1,0,1,0,0,1,1,1,0,0,1,1],
  [-1,3,-3,4,-4,2,-4,1,-3,0,0,0,1,0,1,-1,1,2,1,1,1,2,1,1,1,1],
  [-1,0,0,1,0,0,1],
  [1,-1,0,-1,-1,0,0,-1,0,0,-1,1,0,0,1,1,1,0,0,1,1],
  [1,1,2,1,1,1],
  [1,0,0,0,1,2,0,-3,0,1,-1,-3,0,2,1,-1,0,2,1],
  [-1,1,1,0,1,1],
  [-1,1,-1,0,0,1,-1,1,0,1,-1,1,0,1,0,0,0,1],
  [-1,2,0,0,0,1,-1,-2,-1,0,-3,-2,1,0,-1,1,1,2,1,1,1,2,1,1,1,1],
  [1,0,-1,-1,0,0,0,0,-1,-1,0,2,1,0,-1,0,1,1],
  [-1,0,0,-1,1,0,1,1],
  [1,-2,1,-1,-1,0,-2,1,-1,1,-1,1,0,1,0,0,0,1],
  [1,1,1,0,1,1],
  [-1,-1,-1,1,-1,-1,1,0,1,0,0,1,1,0,0,1,1,1,0,0,1,1],
  [-1,-1,0,-1,0,1,2,2,3,2,2,2,1],
  [1,1,1,0,0,0,1],
  [-1,0,-1,2,-1,2,-3,3,-2,3,-2,2,-1,2,-1,1,-1,1,0,0,1],
  [1,-2,1,-2,2,-3,1,-2,1,-1,-1,0,0,2,1,2,0,2,-1,1,1,2,1,1,1],
  [-1,-1,0,1,1,1],
  [-1,0,0,0,-1,-1,0,0,0,-1,1,1,1,0,0,0,1,0,1,1],
  [-1,-2,-3,-3,-3,-3,-4,-3,-2,-1,0,1,1,3,3,2,2,1],
  [-1,2,-1,1,-1,1],
  [-1,-1,-1,0,0,1,1,1,0,1,1,1,0,0,0,1,0,1,1],
  [1,-1,1,0,1],
  [-1,0,1,0,0,0,1],
  [-1,1,1,-1,-1,-2,1,0,0,0,0,0,1,1,1,0,0,0,1,0,1,1],
  [1,0,-1,-1,-1,0,-1,0,0,0,-1,1,1,1,0,0,0,1,0,1,1],
  [1,-1,-1,2,0,0,1,-1,0,0,-1,0,0,-1,0,2,-1,1,1],
  [-1,1,0,1,1,1],
  [-1,1,0,-1,0,2,-2,0,2,-1,0,2,-1,-1,2,-1,0,1],
  [-1,3,-3,3,-3,4,-5,3,-3,2,-5,0,-2,0,1,2,2,0,2,-1,1,1,2,1,1,1],
  [1,-1,0,0,0,-1,0,-1,-1,-1,0,1,1,1,0,0,0,1,0,1,1],
  [-1,-1,1,1,-1,-2,1,1,0,0,2,1],
  [1,-1,-1,-1,0,-1,-2,-1,-1,0,0,1,1,0,0,0,1,0,1,1],
  [1,1,0,1,1,1],
  [-1,-1,1,-1,-1,-1,1,1,0,0,0,1,1,1,1,0,0,0,1,0,1,1],
  [1,2,1,1,1,1],
  [-1,-1,0,0,0,-1,1,1,3,2,3,2,2,2,3,3,2,2,1],
  [-1,0,1,1,1,1],
  [-1,1,-1,1,-1,0,1,0,1,0,0,0,0,0,1,-1,1,0,0,1],
  [1,-2,1,-2,1,-1,0,0,0,-1,1,0,0,1,0,1,1,2,1,1,1],
  [-1,1,-1,1,-1,0,0,0,0,1,-1,1,0,0,1],
  [1,0,1,-2,1,-1,1,0,-1,-1,-1,0,-1,0,-1,0,0,2,1,1,1],
  [1,0,1,1,1,1],
  [-1,1,0,0,0,0,1],
  [-1,1,-1,-1,-1,-1,1,1,1,1,1,0,0,0,0,1,0,0,1,0,1,1],
  [-1,0,0,0,1,-1,1,-1,1,-1,2,0,2,1,1,2,1,1,1],
  [-1,1,1,1,1,1],
  [-1,0,0,0,0,1,0,0,0,1,0,0,1,0,1,1],
  [1,-1,0,0,-1,0,0,0,0,-1,2,-2,2,-1,1,0,1,1,0,1],
  [-1,0,1,2,2,3,3,2,2,1],
  [-1,0,1,3,3,2,1,1,2,2,2,1]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hints : Array Hint := #[
  .positive 1 [(0,false,1),(1,false,1),(2,false,1)],
  .positive 1 [(3,false,1)],
  .positive 1 [(4,true,1)],
  .positive 1 [],
  .positive 1 [(4,true,1),(5,false,1)],
  .positive 1 [(0,false,1),(7,false,1)],
  .positive 1 [(8,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(6,true,1)],
  .positive 1 [(3,false,1),(0,false,1),(9,false,1),(10,false,1)],
  .root 6 0,
  .positive 1 [(0,false,1),(6,false,1)],
  .positive 1 [(3,false,2)],
  .positive 1 [(4,true,1),(0,false,1)],
  .positive 1 [(3,false,1),(4,true,1),(0,false,1),(11,false,1),(2,false,1)],
  .positive 1 [(12,false,1)],
  .positive 1 [(3,false,1),(8,false,1),(13,true,1)],
  .positive 1 [(4,true,1),(3,false,1)],
  .positive 1 [(3,false,7),(4,true,1),(14,false,1)],
  .positive 1 [(15,false,1)],
  .positive 1 [(0,false,1)],
  .positive 1 [(4,true,1),(0,false,1),(9,false,1),(16,false,1),(15,false,1)],
  .positive 1 [(17,false,1)],
  .positive 1 [(3,false,3),(0,false,1),(15,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(15,false,1),(8,false,1),(18,true,1)],
  .positive 1 [(3,false,1),(0,false,1)],
  .positive 1 [(4,true,1),(9,false,1),(19,false,1),(0,false,2)],
  .positive 1 [(2,false,1),(20,false,1)],
  .positive 1 [(0,false,1),(10,false,1),(21,true,1),(8,false,1)],
  .positive 1 [(0,false,1),(22,false,1)],
  .positive 1 [(23,true,1),(0,false,2)],
  .positive 1 [(25,false,1),(26,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(1,false,1),(26,false,1),(24,true,1),(25,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(15,false,1),(27,false,1)],
  .positive 1 [(0,false,1),(10,false,1),(21,false,1)],
  .root 24 28,
  .positive 1 [(3,false,1),(0,false,1),(1,false,1),(24,false,1)],
  .positive 1 [(3,false,3)],
  .positive 1 [(4,true,1),(2,false,1)],
  .positive 1 [(3,false,2),(4,true,1),(29,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(30,false,1)],
  .positive 1 [(3,false,2),(8,false,1),(31,true,1)],
  .positive 1 [(3,false,1),(4,true,1),(0,false,1)],
  .positive 1 [(3,false,8),(4,true,1),(32,false,1)],
  .positive 1 [(0,false,1),(1,false,1)],
  .positive 1 [(4,true,1),(0,false,1),(33,false,1)],
  .positive 1 [(34,false,1)],
  .positive 1 [(3,false,2),(35,false,1)],
  .positive 1 [(3,false,1),(8,false,1),(36,true,1)],
  .positive 1 [(3,false,1),(15,false,1)],
  .positive 1 [(4,true,1),(0,false,1),(37,false,1),(15,false,1)],
  .positive 1 [(38,false,1)],
  .positive 1 [(39,true,1),(15,false,1),(2,false,1),(8,false,1)],
  .positive 1 [(40,false,1)],
  .positive 1 [(0,false,1),(15,false,1),(41,true,1)],
  .positive 1 [(3,false,2),(26,false,1),(25,false,1),(42,true,1)],
  .positive 1 [(4,true,1),(3,false,2)],
  .positive 1 [(3,false,7),(0,false,1),(4,true,1),(15,false,1),(43,false,1)],
  .positive 1 [(26,false,1)],
  .positive 1 [(2,false,1)],
  .positive 1 [(3,false,1),(4,true,1),(44,false,1)],
  .positive 1 [(25,false,1)],
  .positive 1 [(45,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(1,false,1),(2,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(46,true,1)],
  .positive 1 [(0,false,1),(3,false,2)],
  .positive 1 [(4,true,1),(0,false,2)],
  .positive 1 [(3,false,1),(4,true,1),(47,false,1),(0,false,2)],
  .positive 1 [(48,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(8,false,1),(49,true,1)],
  .positive 1 [(0,false,1),(50,false,1)],
  .positive 1 [(3,false,1),(51,true,1),(0,false,2)],
  .positive 1 [(3,false,1),(17,false,1)],
  .positive 1 [(0,false,1),(25,false,1),(52,true,1),(26,false,1)],
  .positive 1 [(53,false,1)],
  .positive 1 [(4,true,1),(0,false,1),(54,false,1)],
  .positive 1 [(30,false,1)],
  .positive 1 [(3,false,4),(2,false,1)],
  .positive 1 [(3,false,3),(2,false,1),(8,false,1),(55,true,1)],
  .positive 1 [(3,false,1),(15,false,1),(25,false,1)],
  .positive 1 [(0,false,1),(56,true,1)],
  .positive 1 [(25,false,1),(57,true,1),(26,false,1)],
  .positive 1 [(3,false,1),(2,false,1)],
  .positive 1 [(4,true,1),(2,false,1),(58,false,1)],
  .positive 1 [(0,false,1),(50,true,1)],
  .positive 1 [(3,false,3),(0,false,1),(2,false,1),(59,true,1)],
  .root 50 60,
  .positive 1 [(0,false,1),(61,true,1),(2,false,1),(8,false,1)],
  .positive 1 [(62,true,1)],
  .positive 1 [(3,false,3),(0,false,1),(2,false,1),(63,true,1)],
  .root 62 64,
  .positive 1 [(62,false,1)],
  .positive 1 [(0,false,1),(2,false,1),(65,true,1)],
  .positive 1 [(4,true,1),(0,false,1),(15,false,1),(2,false,1)],
  .positive 1 [(3,false,1),(4,true,1),(66,true,1),(0,false,2)],
  .positive 1 [(3,false,4)],
  .positive 1 [(0,false,1),(4,true,1),(15,false,1)],
  .positive 1 [(3,false,3),(0,false,1),(4,true,1),(67,false,1)],
  .positive 1 [(68,false,1)],
  .positive 1 [(3,false,3),(8,false,1),(69,true,1)],
  .positive 1 [(3,false,1),(4,true,1),(2,false,1)],
  .positive 1 [(3,false,9),(4,true,1),(70,false,1)],
  .positive 1 [(20,false,1)],
  .positive 1 [(3,false,2),(1,false,1),(0,false,2)],
  .positive 1 [(3,false,1),(0,false,1),(8,false,1),(71,true,1)],
  .positive 1 [(3,false,1),(0,false,1),(1,false,1)],
  .positive 1 [(4,true,1),(72,false,1),(0,false,2)],
  .positive 1 [(73,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(74,true,1)],
  .positive 1 [(3,false,3),(0,false,1),(75,true,1)],
  .positive 1 [(0,false,1),(76,false,1)],
  .positive 1 [(3,false,3),(0,false,1),(25,false,1),(26,false,1),(77,true,1)],
  .positive 1 [(3,false,2),(4,true,1),(0,false,1)],
  .positive 1 [(3,false,7),(4,true,1),(78,false,1),(0,false,2)],
  .positive 1 [(79,false,1)],
  .positive 1 [(80,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(81,true,1)],
  .positive 1 [(3,false,2),(15,false,1)],
  .positive 1 [(4,true,1),(82,false,1)],
  .positive 1 [(3,false,1),(4,true,1),(0,false,1),(83,false,1)],
  .positive 1 [(1,false,1),(2,false,1),(17,false,1)],
  .positive 1 [(3,false,1),(8,false,1),(84,true,1)],
  .positive 1 [(85,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(86,true,1)],
  .positive 1 [(3,false,1),(34,false,1)],
  .positive 1 [(26,false,1),(87,true,1),(25,false,1)],
  .positive 1 [(3,false,7),(0,false,1),(4,true,1),(88,false,1)],
  .positive 1 [(0,false,1),(89,false,1)],
  .positive 1 [(3,false,3),(53,false,1)],
  .positive 1 [(3,false,2),(8,false,1),(90,true,1)],
  .positive 1 [(3,false,1),(0,false,1),(20,false,1)],
  .positive 1 [(0,false,1),(91,true,1)],
  .positive 1 [(25,false,1),(26,false,1),(92,true,1)],
  .positive 1 [(4,true,1),(0,false,1),(93,false,1)],
  .positive 1 [(3,false,1),(26,false,1)],
  .positive 1 [(8,false,1),(94,true,1)],
  .positive 1 [(95,true,1)],
  .positive 1 [(3,false,2),(0,false,1),(96,true,1)],
  .root 95 64,
  .positive 1 [(95,false,1)],
  .positive 1 [(0,false,1),(97,true,1)],
  .positive 1 [(4,true,1),(98,false,1)],
  .positive 1 [(3,false,1),(4,true,1),(99,false,1)],
  .positive 1 [(3,false,3),(0,false,1)],
  .positive 1 [(100,true,1)],
  .positive 1 [(3,false,2),(0,false,1),(101,true,1)],
  .root 100 64,
  .positive 1 [(100,false,1)],
  .positive 1 [(102,false,1)],
  .positive 1 [(0,false,1),(2,false,1),(1,false,1),(103,true,1)],
  .positive 1 [(4,true,1),(0,false,1),(2,false,1)],
  .positive 1 [(3,false,2),(4,true,1),(104,false,1),(0,false,2)],
  .positive 1 [(105,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(8,false,1),(106,true,1)],
  .positive 1 [(0,false,1),(1,false,1),(25,false,1)],
  .positive 1 [(3,false,2),(107,true,1),(0,false,2)],
  .positive 1 [(3,false,1),(25,false,1)],
  .positive 1 [(0,false,1),(108,true,1)],
  .positive 1 [(0,false,1),(25,false,1),(26,false,1),(109,true,1)],
  .positive 1 [(3,false,1),(4,true,1),(0,false,2)],
  .positive 1 [(3,false,8),(4,true,1),(110,false,1),(0,false,2)],
  .positive 1 [(15,false,1),(17,false,1)],
  .positive 1 [(3,false,2),(111,false,1)],
  .positive 1 [(3,false,1),(8,false,1),(112,true,1)],
  .positive 1 [(113,false,1)],
  .positive 1 [(3,false,2),(9,false,1)],
  .positive 1 [(3,false,1),(9,false,1),(114,true,1)],
  .positive 1 [(3,false,1),(115,false,1)],
  .positive 1 [(25,false,1),(116,true,1),(26,false,1)],
  .positive 1 [(4,true,1),(117,false,1)],
  .positive 1 [(4,true,1),(0,false,1),(118,false,1)],
  .positive 1 [(3,false,1),(53,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(119,true,1)],
  .positive 1 [(120,false,1)],
  .positive 1 [(0,false,1),(121,true,1)],
  .positive 1 [(0,false,1),(4,true,1),(9,false,1)],
  .positive 1 [(122,true,1),(4,true,2),(0,false,2)],
  .positive 1 [(0,false,1),(34,false,1)],
  .positive 1 [(3,false,1),(2,false,1),(123,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(124,true,1)],
  .positive 1 [(125,false,1)],
  .positive 1 [(10,false,1),(0,false,2)],
  .positive 1 [(3,false,1),(0,false,1),(9,false,1),(126,true,1)],
  .positive 1 [(3,false,5),(0,false,1)],
  .positive 1 [(3,false,4),(0,false,1),(25,false,1),(26,false,1),(127,true,1)],
  .positive 1 [(4,true,1),(128,false,1),(0,false,2)],
  .positive 1 [(3,false,2),(2,false,1)],
  .positive 1 [(129,false,1)],
  .positive 1 [(3,false,1),(15,false,1),(130,true,1),(8,false,1)],
  .positive 1 [(3,false,1),(30,false,1)],
  .positive 1 [(0,false,1),(131,true,1)],
  .positive 1 [(132,false,1)],
  .positive 1 [(26,false,1),(25,false,1),(133,true,1)],
  .positive 1 [(4,true,1),(2,false,1),(53,false,1)],
  .positive 1 [(4,true,1),(0,false,1),(134,false,1)],
  .positive 1 [(135,false,1)],
  .positive 1 [(3,false,4),(0,false,1),(8,false,1),(136,true,1)],
  .positive 1 [(3,false,1),(137,true,1)],
  .positive 1 [(138,false,1)],
  .positive 1 [(0,false,1),(139,true,1)],
  .positive 1 [(3,false,1),(0,false,1),(15,false,1)],
  .root 137 3,
  .positive 1 [(3,false,7),(0,false,1),(9,false,1),(140,true,1)],
  .positive 1 [(3,false,1),(137,false,1)],
  .positive 1 [(0,false,1),(25,false,1),(26,false,1),(141,true,1)],
  .positive 1 [(3,false,1),(4,true,1),(15,false,1),(0,false,2)],
  .positive 1 [(3,false,7),(0,false,1),(4,true,1),(142,false,1)],
  .positive 1 [(132,true,1)],
  .positive 1 [(3,false,4),(0,false,1),(143,true,1)],
  .positive 1 [(9,false,1)],
  .root 132 144,
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(145,true,1)],
  .positive 1 [(3,false,4),(4,true,1),(146,false,1),(0,false,2)],
  .positive 1 [(3,false,5)],
  .positive 1 [(4,true,1),(9,false,1)],
  .positive 1 [(3,false,4),(4,true,1),(147,false,1)],
  .positive 1 [(0,false,1),(148,false,1)],
  .positive 1 [(3,false,4),(0,false,1),(8,false,1),(149,false,1),(150,true,1)],
  .positive 1 [(3,false,1),(0,false,1),(4,true,1),(15,false,1)],
  .positive 1 [(3,false,10),(0,false,1),(4,true,1),(151,false,1)],
  .positive 1 [(1,false,1),(25,false,1)],
  .positive 1 [(3,false,2),(152,false,1)],
  .positive 1 [(3,false,1),(8,false,1),(153,true,1)],
  .positive 1 [(3,false,1),(154,false,1)],
  .positive 1 [(0,false,1),(4,true,1),(155,false,1)],
  .positive 1 [(2,false,1),(156,false,1)],
  .positive 1 [(8,false,1),(157,true,1)],
  .positive 1 [(3,false,4),(158,true,1),(0,false,2)],
  .positive 1 [(159,false,1)],
  .positive 1 [(3,false,4),(15,false,1),(25,false,1),(160,true,1),(26,false,1)],
  .positive 1 [(3,false,2),(4,true,1),(2,false,1)],
  .positive 1 [(3,false,15),(4,true,1),(161,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(1,false,1)],
  .positive 1 [(76,true,1)],
  .positive 1 [(3,false,1),(162,true,1)],
  .root 76 64,
  .positive 1 [(76,false,1)],
  .positive 1 [(163,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(164,true,1)],
  .positive 1 [(0,false,1),(4,true,1),(26,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(4,true,1),(165,false,1)],
  .positive 1 [(166,false,1)],
  .positive 1 [(3,false,1),(8,false,1),(167,true,1)],
  .positive 1 [(0,false,1),(168,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(169,true,1)],
  .positive 1 [(3,false,1),(20,false,1)],
  .positive 1 [(25,false,1),(26,false,1),(170,true,1)],
  .positive 1 [(3,false,7),(0,false,1),(4,true,1),(15,false,1),(171,false,1)],
  .positive 1 [(172,false,1)],
  .positive 1 [(3,false,3),(26,false,1)],
  .positive 1 [(3,false,2),(8,false,1),(173,true,1)],
  .positive 1 [(174,false,1)],
  .positive 1 [(3,false,1),(9,false,1),(175,true,1)],
  .positive 1 [(3,false,1),(176,false,1)],
  .positive 1 [(26,false,1),(25,false,1),(154,false,1),(177,true,1)],
  .positive 1 [(0,false,1),(4,true,1),(178,false,1)],
  .positive 1 [(3,false,1),(179,false,1)],
  .positive 1 [(180,true,1),(8,false,1)],
  .positive 1 [(181,false,1)],
  .positive 1 [(3,false,1),(25,false,1),(26,false,1),(182,true,1)],
  .positive 1 [(4,true,1),(0,false,1),(183,false,1)],
  .positive 1 [(3,false,1),(4,true,1),(184,false,1)],
  .positive 1 [(3,false,3),(15,false,1)],
  .positive 1 [(22,true,1)],
  .positive 1 [(3,false,2),(15,false,1),(185,true,1)],
  .root 22 64,
  .positive 1 [(22,false,1)],
  .positive 1 [(186,false,1)],
  .positive 1 [(0,false,1),(2,false,1),(1,false,1),(187,true,1)],
  .positive 1 [(4,true,1),(188,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(4,true,1),(15,false,1),(189,false,1)],
  .positive 1 [(190,false,1)],
  .positive 1 [(3,false,2),(15,false,1),(8,false,1),(191,true,1)],
  .positive 1 [(192,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(15,false,1),(193,true,1)],
  .positive 1 [(3,false,1),(79,false,1)],
  .positive 1 [(0,false,1),(194,true,1)],
  .positive 1 [(26,false,1),(20,false,1),(25,false,1),(154,false,1),(195,true,1)],
  .positive 1 [(3,false,1),(4,true,1),(82,false,1)],
  .positive 1 [(3,false,8),(4,true,1),(0,false,1),(15,false,1),(2,false,1),(196,false,1)],
  .positive 1 [(7,false,1)],
  .positive 1 [(3,false,2),(1,false,1),(2,false,1)],
  .positive 1 [(3,false,1),(8,false,1),(197,true,1)],
  .positive 1 [(15,false,1),(154,false,1)],
  .positive 1 [(3,false,1),(9,false,1),(198,true,1),(199,false,1),(15,false,2)],
  .positive 1 [(3,false,1),(7,false,1)],
  .positive 1 [(25,false,1),(200,true,1),(26,false,1)],
  .positive 1 [(4,true,1),(15,false,1),(2,false,1)],
  .positive 1 [(0,false,1),(4,true,1),(15,false,1),(201,false,1)],
  .positive 1 [(202,false,1)],
  .positive 1 [(0,false,1),(2,false,1),(1,false,1),(203,true,1)],
  .positive 1 [(3,false,2),(0,false,1),(15,false,1),(204,true,1)],
  .positive 1 [(205,false,1)],
  .positive 1 [(3,false,2),(206,true,1),(25,false,1),(15,false,1),(26,false,1)],
  .positive 1 [(4,true,1),(2,false,1),(26,false,1)],
  .positive 1 [(0,false,1),(4,true,1),(207,false,1)],
  .positive 1 [(176,false,1)],
  .positive 1 [(3,false,1),(208,false,1)],
  .positive 1 [(209,true,1),(8,false,1)],
  .positive 1 [(3,false,4),(15,false,1)],
  .positive 1 [(3,false,3),(0,false,1),(210,true,1),(15,false,2)],
  .positive 1 [(211,false,1)],
  .positive 1 [(3,false,3),(15,false,1),(25,false,1),(26,false,1),(212,true,1)],
  .positive 1 [(0,false,1),(4,true,1),(213,false,1)],
  .positive 1 [(3,false,2),(26,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(34,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(214,true,1),(8,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(89,false,1)],
  .positive 1 [(215,true,1),(0,false,2)],
  .positive 1 [(216,false,1)],
  .positive 1 [(0,false,1),(25,false,1),(26,false,1),(217,true,1)],
  .positive 1 [(4,true,1),(0,false,1),(15,false,2)],
  .positive 1 [(4,true,1),(15,false,1),(218,false,1),(0,false,2)],
  .positive 1 [(219,false,1)],
  .positive 1 [(3,false,3),(15,false,1),(8,false,1),(220,true,1)],
  .positive 1 [(3,false,1),(152,false,1)],
  .positive 1 [(3,false,1),(22,false,1)],
  .positive 1 [(3,false,7),(9,false,1),(221,true,1)],
  .positive 1 [(26,false,1),(25,false,1),(222,true,1)],
  .positive 1 [(3,false,1),(4,true,1),(188,false,1)],
  .positive 1 [(3,false,9),(0,false,1),(4,true,1),(15,false,1),(223,false,1)],
  .positive 1 [(216,true,1)],
  .positive 1 [(3,false,3),(15,false,1),(224,true,1)],
  .positive 1 [(225,false,1)],
  .root 216 144,
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(226,true,1)],
  .positive 1 [(3,false,3),(4,true,1),(0,false,1),(227,false,1),(15,false,1)],
  .positive 1 [(3,false,4),(0,false,1)],
  .positive 1 [(137,true,1)],
  .positive 1 [(3,false,3),(0,false,1),(228,true,1)],
  .root 137 64,
  .positive 1 [(137,false,1)],
  .positive 1 [(229,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(230,true,1)],
  .positive 1 [(4,true,1),(15,false,1),(0,false,2)],
  .positive 1 [(3,false,3),(4,true,1),(231,false,1),(0,false,2)],
  .positive 1 [(2,false,1),(232,false,1)],
  .positive 1 [(3,false,3),(0,false,1),(2,false,1),(8,false,1),(233,true,1)],
  .positive 1 [(0,false,1),(234,false,1)],
  .positive 1 [(3,false,3),(235,true,1),(0,false,2)],
  .positive 1 [(3,false,1),(100,false,1)],
  .positive 1 [(236,true,1),(0,false,1),(26,false,1),(25,false,1)],
  .positive 1 [(3,false,1),(4,true,1),(0,false,1),(2,false,1)],
  .positive 1 [(3,false,9),(4,true,1),(154,false,1),(62,false,1),(0,false,2)],
  .positive 1 [(115,false,1)],
  .positive 1 [(3,false,2),(179,false,1)],
  .positive 1 [(3,false,1),(8,false,1),(237,true,1)],
  .positive 1 [(3,false,1),(172,false,1)],
  .positive 1 [(238,true,1),(0,false,1)],
  .positive 1 [(239,true,1),(26,false,1),(25,false,1)],
  .positive 1 [(4,true,1),(240,false,1)],
  .positive 1 [(4,true,1),(0,false,1),(241,false,1)],
  .positive 1 [(3,false,1),(111,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(242,true,1)],
  .positive 1 [(3,false,3),(243,true,1),(0,false,2)],
  .positive 1 [(244,false,1)],
  .positive 1 [(3,false,3),(0,false,1),(26,false,1),(245,true,1),(25,false,1)],
  .positive 1 [(0,false,1),(4,true,1),(152,false,1)],
  .positive 1 [(4,true,1),(246,false,1),(0,false,2)],
  .positive 1 [(0,false,1),(20,false,1)],
  .positive 1 [(3,false,1),(247,false,1)],
  .positive 1 [(0,false,1),(2,false,1),(8,false,1),(248,true,1)],
  .positive 1 [(3,false,3),(0,false,1),(1,false,1)],
  .positive 1 [(3,false,2),(249,true,1),(0,false,2)],
  .positive 1 [(250,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(25,false,1),(26,false,1),(10,false,1),(251,true,1)],
  .positive 1 [(4,true,1),(252,false,1),(0,false,2)],
  .positive 1 [(3,false,2),(53,false,1)],
  .positive 1 [(253,false,1)],
  .positive 1 [(3,false,1),(8,false,1),(254,true,1)],
  .positive 1 [(3,false,1),(15,false,1),(17,false,1)],
  .positive 1 [(0,false,1),(255,true,1)],
  .positive 1 [(256,false,1)],
  .positive 1 [(25,false,1),(257,true,1),(26,false,1)],
  .positive 1 [(4,true,1),(258,false,1)],
  .positive 1 [(0,false,1),(4,true,1),(15,false,1),(259,false,1)],
  .positive 1 [(260,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(261,true,1),(8,false,1)],
  .positive 1 [(3,false,1),(76,false,1)],
  .positive 1 [(0,false,1),(262,true,1)],
  .positive 1 [(0,false,1),(1,false,1),(25,false,1),(26,false,1),(263,true,1)],
  .positive 1 [(3,false,1),(0,false,1),(4,true,1),(26,false,1)],
  .positive 1 [(3,false,8),(4,true,1),(264,false,1),(154,false,1),(0,false,2)],
  .positive 1 [(256,true,1)],
  .positive 1 [(3,false,2),(0,false,1),(265,true,1)],
  .positive 1 [(266,false,1)],
  .root 256 144,
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(267,true,1)],
  .positive 1 [(3,false,2),(4,true,1),(10,false,1),(268,false,1),(0,false,2)],
  .positive 1 [(15,false,1),(25,false,1)],
  .positive 1 [(269,false,1)],
  .positive 1 [(1,false,1),(2,false,1),(270,true,1),(0,false,2)],
  .positive 1 [(3,false,2),(154,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(271,true,1)],
  .positive 1 [(272,false,1)],
  .positive 1 [(3,false,1),(26,false,1),(25,false,1),(273,true,1)],
  .positive 1 [(4,true,1),(2,false,2)],
  .positive 1 [(0,false,1),(2,false,1),(274,true,1),(4,true,2)],
  .positive 1 [(3,false,3),(2,false,1)],
  .positive 1 [(0,false,1),(275,false,1)],
  .positive 1 [(3,false,2),(8,false,1),(276,true,1)],
  .positive 1 [(0,false,1),(277,false,1)],
  .positive 1 [(278,false,1)],
  .positive 1 [(3,false,1),(9,false,1),(279,true,1)],
  .positive 1 [(3,false,1),(0,false,1),(34,false,1)],
  .positive 1 [(280,true,1),(26,false,1),(25,false,1)],
  .positive 1 [(4,true,1),(0,false,1),(1,false,1),(2,false,1)],
  .positive 1 [(0,false,1),(4,true,1),(2,false,1),(281,false,1)],
  .positive 1 [(282,false,1)],
  .positive 1 [(3,false,1),(2,false,1),(8,false,1),(283,true,1)],
  .positive 1 [(3,false,1),(1,false,1),(25,false,1)],
  .positive 1 [(0,false,1),(284,true,1)],
  .positive 1 [(285,true,1),(26,false,1),(25,false,1)],
  .positive 1 [(3,false,1),(4,true,1),(9,false,1)],
  .positive 1 [(3,false,7),(4,true,1),(0,false,1),(15,false,1),(286,false,1)],
  .positive 1 [(278,true,1)],
  .positive 1 [(3,false,1),(287,true,1)],
  .positive 1 [(288,false,1)],
  .root 278 144,
  .positive 1 [(0,false,1),(2,false,1),(1,false,1),(289,true,1)],
  .positive 1 [(4,true,1),(290,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(4,true,1),(291,false,1)],
  .positive 1 [(292,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(10,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(293,true,1)],
  .positive 1 [(3,false,6)],
  .positive 1 [(3,false,5),(0,false,1),(294,true,1)],
  .positive 1 [(0,false,1),(79,false,1)],
  .positive 1 [(3,false,5),(0,false,1),(25,false,1),(26,false,1),(295,true,1)],
  .positive 1 [(3,false,5),(0,false,1),(296,true,1)],
  .positive 1 [(3,false,2),(4,true,1),(0,false,1),(15,false,1)],
  .positive 1 [(3,false,16),(0,false,1),(4,true,1),(15,false,1),(17,false,1)],
  .positive 1 [(297,false,1)],
  .positive 1 [(298,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(299,true,1)],
  .positive 1 [(4,true,1),(300,false,1),(0,false,2)],
  .positive 1 [(301,false,1)],
  .positive 1 [(3,false,5),(8,false,1),(302,true,1)],
  .positive 1 [(3,false,5),(303,true,1),(0,false,2)],
  .positive 1 [(3,false,11),(4,true,1),(304,false,1)],
  .positive 1 [(3,false,5),(0,false,1),(4,true,1),(305,false,1),(1,false,1)]]
end GeometricMaxCut.FinitePoly.F7


namespace GeometricMaxCut.FinitePoly.F7
open GeometricMaxCut FinitePoly Certificate

def tree0 : Tree := (.leaf 0 0 [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree0 (by decide +kernel)

def tree1 : Tree := (.leaf 2 2 [0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree1 (by decide +kernel)

def tree2 : Tree := (.leaf 0 2 [0,1,2,3,4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree2 (by decide +kernel)

def tree3 : Tree := (.signs 6 (.leaf 2 3 [0,0,1,5,6,7]) (.leaf 4 4 [8,9]) (.leaf 4 4 [8,10]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w3 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree3 (by decide +kernel)

def tree4 : Tree := (.leaf 0 2 [0,11,12,3,13])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w4 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,true,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree4 (by decide +kernel)

def tree5 : Tree := (.bisect (.bisect (.bisect (.leaf 2 3 [0,0,11,14,6,15]) (.leaf 2 4 [0,8,10,11,16,1,17])) (.leaf 0 4 [8,10,18,16,19,20])) (.leaf 0 4 [8,10,18,16,19,20]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,true,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree5 (by decide +kernel)

def tree6 : Tree := (.bisect (.leaf 2 3 [0,0,21,22,6,23]) (.leaf 0 4 [8,10,24,12,19,25]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w6 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,true,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree6 (by decide +kernel)

def tree7 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,24,26,6,27]) (.leaf 2 5 [0,8,10,24,28,5,29])) (.signs 24 (.leaf 4 5 [8,10,8,10,11,28,30,31]) (.leaf 6 6 [32,33,34]) (.leaf 6 6 [32,33,35])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w7 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,true,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree7 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F7


namespace GeometricMaxCut.FinitePoly.F7
open GeometricMaxCut FinitePoly Certificate

def tree8 : Tree := (.leaf 0 2 [0,36,37,3,38])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w8 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,false,true,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree8 (by decide +kernel)

def tree9 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,36,39,6,40]) (.leaf 2 4 [0,8,10,36,41,1,42])) (.leaf 0 4 [8,10,43,41,19,44]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w9 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,false,true,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree9 (by decide +kernel)

def tree10 : Tree := (.bisect (.leaf 2 3 [0,0,45,46,6,47]) (.leaf 0 4 [8,10,48,37,19,49]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w10 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,false,true,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree10 (by decide +kernel)

def tree11 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,48,50,6,51]) (.leaf 2 5 [0,8,10,48,52,5,53])) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,36,52,30,54]) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,36,52,30,54]) (.leaf 2 6 [0,32,33,35,48,55,24,56])) (.leaf 2 6 [0,32,33,35,48,55,24,56]))) (.leaf 0 6 [32,33,35,57,55,58,59])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w11 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,false,true,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree11 (by decide +kernel)

def tree12 : Tree := (.bisect (.leaf 2 1 [0,60,61,62,63]) (.leaf 0 4 [8,10,64,65,19,66]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w12 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,true,true,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree12 (by decide +kernel)

def tree13 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,64,67,6,68]) (.leaf 2 5 [0,8,10,64,69,5,70])) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,71,69,30,72]) (.bisect (.leaf 4 5 [8,10,8,10,71,69,30,72]) (.leaf 0 6 [32,33,35,73,41,58,74]))) (.leaf 0 6 [32,33,35,73,41,58,74])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w13 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,true,true,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree13 (by decide +kernel)

def tree14 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,75,76,6,77]) (.leaf 2 5 [0,8,10,75,78,5,79])) (.bisect (.leaf 4 5 [8,10,8,10,60,78,30,80]) (.leaf 0 6 [32,33,35,81,37,58,82])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w14 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,true,true,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree14 (by decide +kernel)

def tree15 : Tree := (.bisect (.signs 50 (.leaf 3 1 [0,83,76,3,84]) (.leaf 3 1 [0,85,76,3,84]) (.leaf 2 3 [0,0,81,69,6,86])) (.bisect (.signs 62 (.leaf 5 1 [8,10,87,76,19,88]) (.leaf 5 1 [8,10,89,76,19,88]) (.leaf 2 5 [0,8,10,81,90,5,91])) (.leaf 7 5 [32,33,35,8,10,92,90,11,93])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w15 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,true,true,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree15 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F7


namespace GeometricMaxCut.FinitePoly.F7
open GeometricMaxCut FinitePoly Certificate

def tree16 : Tree := (.leaf 0 2 [0,94,95,3,96])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w16 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,false,false,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree16 (by decide +kernel)

def tree17 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,94,97,6,98]) (.leaf 2 4 [0,8,10,94,99,1,100])) (.leaf 2 4 [0,8,10,94,99,1,100]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w17 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,false,false,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree17 (by decide +kernel)

def tree18 : Tree := (.bisect (.leaf 2 3 [0,0,101,102,6,103]) (.leaf 0 4 [8,10,104,95,19,105]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w18 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,false,false,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree18 (by decide +kernel)

def tree19 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,104,106,6,107]) (.leaf 4 3 [8,10,0,94,106,5,108])) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,94,109,30,110]) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,94,109,30,110]) (.leaf 2 6 [0,32,33,35,104,111,24,112])) (.leaf 2 6 [0,32,33,35,104,111,24,112]))) (.leaf 2 6 [0,32,33,35,104,111,24,112])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w19 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,false,false,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree19 (by decide +kernel)

def tree20 : Tree := (.bisect (.leaf 2 1 [0,113,114,62,115]) (.leaf 0 4 [8,10,116,117,19,118]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w20 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,true,false,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree20 (by decide +kernel)

def tree21 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,116,119,6,120]) (.leaf 2 5 [0,8,10,116,121,5,122])) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,123,121,30,124]) (.bisect (.leaf 4 5 [8,10,8,10,123,121,30,124]) (.leaf 2 6 [0,32,33,35,116,99,24,125]))) (.leaf 2 6 [0,32,33,35,116,99,24,125])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w21 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,true,false,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree21 (by decide +kernel)

def tree22 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,126,127,6,128]) (.leaf 2 5 [0,8,10,126,129,5,130])) (.bisect (.leaf 4 5 [8,10,8,10,113,129,30,131]) (.leaf 2 6 [0,32,33,35,126,95,24,132])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w22 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,true,false,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree22 (by decide +kernel)

def tree23 : Tree := (.bisect (.leaf 2 3 [0,0,133,121,6,134]) (.bisect (.signs 95 (.leaf 5 1 [8,10,135,127,19,136]) (.leaf 5 1 [8,10,137,127,19,136]) (.leaf 2 5 [0,8,10,133,138,5,139])) (.leaf 7 5 [32,33,35,8,10,140,138,11,141])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w23 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,true,false,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree23 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F7


namespace GeometricMaxCut.FinitePoly.F7
open GeometricMaxCut FinitePoly Certificate

def tree24 : Tree := (.bisect (.signs 100 (.leaf 0 2 [0,142,143,3,144]) (.leaf 0 2 [0,142,145,3,144]) (.leaf 2 1 [0,146,147,62,148])) (.leaf 0 4 [8,10,142,149,19,150]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w24 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,false,true,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree24 (by decide +kernel)

def tree25 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,142,151,6,152]) (.leaf 2 5 [0,8,10,142,153,5,154])) (.bisect (.bisect (.leaf 4 3 [8,10,0,155,151,5,156]) (.bisect (.leaf 4 5 [8,10,8,10,155,153,30,157]) (.leaf 2 6 [0,32,33,35,142,158,24,159]))) (.leaf 2 6 [0,32,33,35,142,158,24,159])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w25 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,false,true,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree25 (by decide +kernel)

def tree26 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,160,161,6,162]) (.leaf 4 1 [8,10,146,163,164,165])) (.bisect (.leaf 4 5 [8,10,8,10,146,166,30,167]) (.leaf 2 6 [0,32,33,35,160,168,24,169])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w26 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,false,true,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree26 (by decide +kernel)

def tree27 : Tree := (.bisect (.leaf 2 3 [0,0,170,153,6,171]) (.bisect (.leaf 2 5 [0,8,10,170,172,5,173]) (.leaf 7 3 [32,33,35,0,174,153,24,175])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w27 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,false,true,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree27 (by decide +kernel)

def tree28 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,176,177,6,178]) (.leaf 4 1 [8,10,179,180,164,181])) (.bisect (.leaf 4 5 [8,10,8,10,179,182,30,183]) (.leaf 2 6 [0,32,33,35,176,149,24,184])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w28 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,true,true,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree28 (by decide +kernel)

def tree29 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,185,186,6,187]) (.leaf 4 3 [8,10,0,188,186,5,189])) (.bisect (.leaf 4 5 [8,10,8,10,188,190,30,191]) (.leaf 7 3 [32,33,35,0,192,186,24,193])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w29 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,true,true,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree29 (by decide +kernel)

def tree30 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,194,182,6,195]) (.signs 137 (.leaf 5 1 [8,10,196,197,19,198]) (.leaf 0 5 [8,10,199,200,164,201]) (.leaf 0 5 [8,10,199,202,164,201]))) (.bisect (.leaf 4 5 [8,10,8,10,176,202,30,203]) (.leaf 7 5 [32,33,35,8,10,204,202,11,205])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w30 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,true,true,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree30 (by decide +kernel)

def tree31 : Tree := (.bisect (.signs 132 (.leaf 3 1 [0,206,182,3,207]) (.leaf 0 3 [0,208,209,62,210]) (.leaf 0 3 [0,208,190,62,210])) (.leaf 5 1 [8,10,174,182,19,211]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w31 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,true,true,true,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree31 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F7


namespace GeometricMaxCut.FinitePoly.F7
open GeometricMaxCut FinitePoly Certificate

def tree32 : Tree := (.leaf 0 2 [0,212,213,3,214])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w32 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,false,false,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree32 (by decide +kernel)

def tree33 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,212,215,6,216]) (.leaf 2 4 [0,8,10,212,217,1,218])) (.leaf 2 4 [0,8,10,212,217,1,218]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w33 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,false,false,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree33 (by decide +kernel)

def tree34 : Tree := (.bisect (.leaf 2 3 [0,0,219,220,6,221]) (.leaf 0 4 [8,10,222,213,19,223]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w34 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,false,false,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree34 (by decide +kernel)

def tree35 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,222,224,6,225]) (.leaf 4 3 [8,10,0,212,224,5,226])) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,212,227,30,228]) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,212,227,30,228]) (.leaf 4 6 [8,10,32,33,35,212,229,11,230])) (.leaf 4 6 [8,10,32,33,35,212,229,11,230]))) (.leaf 4 6 [8,10,32,33,35,212,229,11,230])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w35 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,false,false,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree35 (by decide +kernel)

def tree36 : Tree := (.bisect (.signs 76 (.leaf 0 2 [0,231,232,3,233]) (.leaf 0 2 [0,231,234,3,233]) (.leaf 2 1 [0,235,236,62,237])) (.leaf 0 4 [8,10,231,238,19,239]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w36 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,true,false,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree36 (by decide +kernel)

def tree37 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,231,240,6,241]) (.leaf 2 5 [0,8,10,231,242,5,243])) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,244,242,30,245]) (.bisect (.leaf 4 5 [8,10,8,10,244,242,30,245]) (.leaf 2 6 [0,32,33,35,231,217,24,246]))) (.leaf 2 6 [0,32,33,35,231,217,24,246])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w37 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,true,false,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree37 (by decide +kernel)

def tree38 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,247,248,6,249]) (.leaf 4 1 [8,10,235,250,164,251])) (.bisect (.leaf 4 5 [8,10,8,10,235,252,30,253]) (.leaf 2 6 [0,32,33,35,247,213,24,254])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w38 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,true,false,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree38 (by decide +kernel)

def tree39 : Tree := (.bisect (.leaf 2 3 [0,0,255,242,6,256]) (.bisect (.leaf 4 5 [8,10,8,10,231,257,30,258]) (.leaf 7 5 [32,33,35,8,10,259,257,11,260])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w39 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,true,false,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree39 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F7


namespace GeometricMaxCut.FinitePoly.F7
open GeometricMaxCut FinitePoly Certificate

def tree40 : Tree := (.bisect (.signs 22 (.leaf 0 2 [0,261,262,3,263]) (.leaf 0 2 [0,261,264,3,263]) (.leaf 2 1 [0,265,266,62,267])) (.leaf 0 4 [8,10,261,268,19,269]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w40 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,false,true,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree40 (by decide +kernel)

def tree41 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,261,270,6,271]) (.leaf 2 5 [0,8,10,261,272,5,273])) (.bisect (.bisect (.leaf 4 3 [8,10,0,274,270,5,275]) (.bisect (.leaf 4 5 [8,10,8,10,274,272,30,276]) (.leaf 2 6 [0,32,33,35,261,277,24,278]))) (.leaf 2 6 [0,32,33,35,261,277,24,278])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w41 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,false,true,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree41 (by decide +kernel)

def tree42 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,279,280,6,281]) (.leaf 4 1 [8,10,265,282,164,283])) (.bisect (.leaf 4 5 [8,10,8,10,265,284,30,285]) (.leaf 2 6 [0,32,33,35,279,286,24,287])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w42 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,false,true,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree42 (by decide +kernel)

def tree43 : Tree := (.bisect (.bisect (.leaf 0 3 [0,288,272,62,289]) (.leaf 4 3 [8,10,0,261,272,5,290])) (.bisect (.leaf 4 5 [8,10,8,10,261,291,30,292]) (.leaf 7 3 [32,33,35,0,293,272,24,294])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w43 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,false,true,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree43 (by decide +kernel)

def tree44 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,295,296,6,297]) (.leaf 2 5 [0,8,10,295,298,5,299])) (.bisect (.leaf 4 5 [8,10,8,10,300,298,30,301]) (.leaf 2 6 [0,32,33,35,295,268,24,302])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w44 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,true,true,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree44 (by decide +kernel)

def tree45 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,303,304,6,305]) (.leaf 4 3 [8,10,0,306,304,5,307])) (.bisect (.leaf 4 5 [8,10,8,10,306,308,30,309]) (.leaf 7 3 [32,33,35,0,310,304,24,311])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w45 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,true,true,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree45 (by decide +kernel)

def tree46 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,312,298,6,313]) (.leaf 0 5 [8,10,314,315,164,316])) (.bisect (.leaf 4 5 [8,10,8,10,295,315,30,317]) (.leaf 7 3 [32,33,35,0,318,298,24,319])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w46 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,true,true,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree46 (by decide +kernel)

def tree47 : Tree := (.bisect (.signs 216 (.leaf 3 1 [0,320,298,3,321]) (.leaf 0 3 [0,322,323,62,324]) (.leaf 0 3 [0,322,308,62,324])) (.leaf 5 1 [8,10,293,298,19,325]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w47 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,true,true,false,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree47 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F7


namespace GeometricMaxCut.FinitePoly.F7
open GeometricMaxCut FinitePoly Certificate

def tree48 : Tree := (.bisect (.signs 137 (.leaf 0 2 [0,326,327,3,328]) (.leaf 0 2 [0,326,329,3,328]) (.leaf 2 1 [0,330,331,62,332])) (.leaf 0 4 [8,10,326,333,19,334]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w48 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,false,false,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree48 (by decide +kernel)

def tree49 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,326,335,6,336]) (.leaf 2 5 [0,8,10,326,337,5,338])) (.bisect (.leaf 4 5 [8,10,8,10,339,337,30,340]) (.leaf 2 6 [0,32,33,35,326,341,24,342])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w49 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,false,false,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree49 (by decide +kernel)

def tree50 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,343,344,6,345]) (.leaf 2 5 [0,8,10,343,346,5,347])) (.bisect (.leaf 4 5 [8,10,8,10,330,346,30,348]) (.leaf 2 6 [0,32,33,35,343,349,24,350])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w50 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,false,false,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree50 (by decide +kernel)

def tree51 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,351,337,6,352]) (.leaf 4 3 [8,10,0,326,337,5,353])) (.bisect (.leaf 4 5 [8,10,8,10,326,354,30,355]) (.leaf 7 3 [32,33,35,0,356,337,24,357])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w51 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,false,false,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree51 (by decide +kernel)

def tree52 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,358,359,6,360]) (.leaf 2 5 [0,8,10,358,361,5,362])) (.bisect (.leaf 4 5 [8,10,8,10,363,361,30,364]) (.leaf 2 6 [0,32,33,35,358,333,24,365])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w52 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,true,false,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree52 (by decide +kernel)

def tree53 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,366,367,6,368]) (.leaf 4 3 [8,10,0,369,367,5,370])) (.bisect (.leaf 4 5 [8,10,8,10,369,371,30,372]) (.leaf 7 3 [32,33,35,0,373,367,24,374])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w53 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,true,false,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree53 (by decide +kernel)

def tree54 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,375,361,6,376]) (.leaf 2 5 [0,8,10,375,377,5,378])) (.bisect (.leaf 4 5 [8,10,8,10,358,377,30,379]) (.leaf 7 3 [32,33,35,0,380,361,24,381])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w54 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,true,false,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree54 (by decide +kernel)

def tree55 : Tree := (.bisect (.signs 256 (.leaf 3 1 [0,382,361,3,383]) (.leaf 0 3 [0,384,385,62,386]) (.leaf 0 3 [0,384,371,62,386])) (.leaf 5 1 [8,10,356,361,19,387]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w55 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,true,false,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree55 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F7


namespace GeometricMaxCut.FinitePoly.F7
open GeometricMaxCut FinitePoly Certificate

def tree56 : Tree := (.bisect (.bisect (.leaf 2 1 [0,388,389,62,390]) (.leaf 2 5 [0,8,10,388,391,5,392])) (.bisect (.leaf 4 5 [8,10,8,10,393,391,30,394]) (.leaf 2 6 [0,32,33,35,388,395,24,396])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w56 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,false,true,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree56 (by decide +kernel)

def tree57 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,397,398,6,399]) (.leaf 0 5 [8,10,400,401,164,402])) (.bisect (.leaf 4 5 [8,10,8,10,403,401,30,404]) (.leaf 7 3 [32,33,35,0,405,398,24,406])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w57 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,false,true,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree57 (by decide +kernel)

def tree58 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,407,391,6,408]) (.leaf 2 5 [0,8,10,407,409,5,410])) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,388,409,30,411]) (.bisect (.leaf 4 5 [8,10,8,10,388,409,30,411]) (.leaf 7 3 [32,33,35,0,412,391,24,413]))) (.leaf 7 3 [32,33,35,0,412,391,24,413])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w58 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,false,true,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree58 (by decide +kernel)

def tree59 : Tree := (.bisect (.signs 278 (.leaf 3 1 [0,414,391,3,415]) (.leaf 0 3 [0,416,417,62,418]) (.leaf 0 3 [0,416,401,62,418])) (.leaf 5 1 [8,10,419,391,19,420]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w59 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,false,true,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree59 (by decide +kernel)

def tree60 : Tree := (.bisect (.bisect (.bisect (.leaf 2 3 [0,0,421,422,6,423]) (.leaf 2 5 [0,8,10,421,424,5,425])) (.leaf 2 5 [0,8,10,421,424,5,425])) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,426,424,30,427]) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,426,424,30,427]) (.leaf 6 5 [32,33,35,8,10,393,424,28,428])) (.leaf 7 5 [32,33,35,8,10,429,424,11,430]))) (.leaf 7 5 [32,33,35,8,10,429,424,11,430])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w60 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,false,true,true,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree60 (by decide +kernel)

def tree61 : Tree := (.bisect (.leaf 0 3 [0,431,432,62,433]) (.leaf 5 1 [8,10,405,422,19,434]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w61 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,false,true,true,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree61 (by decide +kernel)

def tree62 : Tree := (.bisect (.bisect (.bisect (.leaf 2 3 [0,0,435,424,6,436]) (.leaf 4 3 [8,10,0,421,424,5,437])) (.leaf 5 3 [8,10,0,412,424,1,438])) (.leaf 5 3 [8,10,0,412,424,1,438]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w62 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [false,true,true,true,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree62 (by decide +kernel)

def tree63 : Tree := (.leaf 3 1 [0,405,424,3,439])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w63 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 7 [true,true,true,true,true,true,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree63 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F7


namespace GeometricMaxCut.FinitePoly
open GeometricMaxCut

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite7 (q : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HullAt q 7 := by
  intro w hw t
  obtain ⟨a,b,c,d,e,f,g,rfl⟩ := seven_word hw
  cases g <;> cases f <;> cases e <;> cases d <;> cases c <;> cases b <;> cases a
  · exact F7.w0 q t ha hq
  · exact F7.w1 q t ha hq
  · exact F7.w2 q t ha hq
  · exact F7.w3 q t ha hq
  · exact F7.w4 q t ha hq
  · exact F7.w5 q t ha hq
  · exact F7.w6 q t ha hq
  · exact F7.w7 q t ha hq
  · exact F7.w8 q t ha hq
  · exact F7.w9 q t ha hq
  · exact F7.w10 q t ha hq
  · exact F7.w11 q t ha hq
  · exact F7.w12 q t ha hq
  · exact F7.w13 q t ha hq
  · exact F7.w14 q t ha hq
  · exact F7.w15 q t ha hq
  · exact F7.w16 q t ha hq
  · exact F7.w17 q t ha hq
  · exact F7.w18 q t ha hq
  · exact F7.w19 q t ha hq
  · exact F7.w20 q t ha hq
  · exact F7.w21 q t ha hq
  · exact F7.w22 q t ha hq
  · exact F7.w23 q t ha hq
  · exact F7.w24 q t ha hq
  · exact F7.w25 q t ha hq
  · exact F7.w26 q t ha hq
  · exact F7.w27 q t ha hq
  · exact F7.w28 q t ha hq
  · exact F7.w29 q t ha hq
  · exact F7.w30 q t ha hq
  · exact F7.w31 q t ha hq
  · exact F7.w32 q t ha hq
  · exact F7.w33 q t ha hq
  · exact F7.w34 q t ha hq
  · exact F7.w35 q t ha hq
  · exact F7.w36 q t ha hq
  · exact F7.w37 q t ha hq
  · exact F7.w38 q t ha hq
  · exact F7.w39 q t ha hq
  · exact F7.w40 q t ha hq
  · exact F7.w41 q t ha hq
  · exact F7.w42 q t ha hq
  · exact F7.w43 q t ha hq
  · exact F7.w44 q t ha hq
  · exact F7.w45 q t ha hq
  · exact F7.w46 q t ha hq
  · exact F7.w47 q t ha hq
  · exact F7.w48 q t ha hq
  · exact F7.w49 q t ha hq
  · exact F7.w50 q t ha hq
  · exact F7.w51 q t ha hq
  · exact F7.w52 q t ha hq
  · exact F7.w53 q t ha hq
  · exact F7.w54 q t ha hq
  · exact F7.w55 q t ha hq
  · exact F7.w56 q t ha hq
  · exact F7.w57 q t ha hq
  · exact F7.w58 q t ha hq
  · exact F7.w59 q t ha hq
  · exact F7.w60 q t ha hq
  · exact F7.w61 q t ha hq
  · exact F7.w62 q t ha hq
  · exact F7.w63 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F7.w63 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w62 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w61 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w60 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w59 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w58 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w57 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w56 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w55 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w54 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w53 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w52 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w51 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w50 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w49 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w48 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w47 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w46 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w45 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w44 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w43 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w42 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w41 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w40 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w39 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w38 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w37 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w36 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w35 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w34 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w33 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w32 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w31 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w30 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w29 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w28 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w27 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w26 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w25 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w24 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w23 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w22 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w21 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w20 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w19 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w18 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w17 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w16 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w15 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w14 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w13 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w12 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w11 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w10 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w9 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w8 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w7 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w6 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w5 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w4 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w3 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w2 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w1 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F7.w0 q (-t) ha hq)

end GeometricMaxCut.FinitePoly


namespace GeometricMaxCut.FinitePoly.F8
open GeometricMaxCut FinitePoly Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def coefficients : Table := #[
  [1,1,1,1,1,1,1],
  [0,1],
  [-1,1],
  [-1,0,1,2,3,4,5,5,4,3,2,1],
  [-1,0,0,0,0,0,0,1,1,1,1,1,1],
  [-1,0,1,1,1,1,1,1],
  [-1,1,1,1,1,1,1,1],
  [1,1],
  [1,0,1],
  [1,-1,1],
  [1,1,1],
  [1,0,-1,0,1],
  [1],
  [-1,1,1],
  [1,1,1,1,1],
  [-1,0,0,0,0,0,1,0,0,0,0,1],
  [-1,0,1,0,1,0,0,0,1,0,1],
  [-1,0,0,1,1,1,1,1],
  [1,0,0,0,1],
  [-1,0,0,0,1,0,1],
  [-1,0,1,0,0,1],
  [-1,0,1,0,1,0,1],
  [-1,0,0,0,0,0,-1,0,0,0,0,0,1,1,1,1,1],
  [1,0,0,0,0,0,1,0,0,0,0,1],
  [-1,1,1,1],
  [-1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1],
  [-1,0,1,1],
  [1,0,0,0,1,1,1,1],
  [-1,1,1,1,-1,-1,-2,-1,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1],
  [-1,1,0,0,1],
  [1,0,0,-1,-1,-1,-1,-1,-1,0,0,0,0,0,1,1,1,1,1,1,1,1],
  [-1,-2,-3,-2,-1,0,1,2,2,2,2,2,2,3,3,3,3,3,3,2,1],
  [-1,0,0,0,1,1,1,1],
  [-1,-1,-1,0,0,0,0,0,0,1,1,1,1,0,1,1,1,1,1,1,1,1],
  [1,1,0,-1,-2,-1,-2,-1,-2,-2,-2,-1,-1,1,0,2,2,2,2,2,2,3,3,3,2,2,1,1],
  [1,0,-1,0,-1,0,0,0,-1,0,-1,1,-1,0,0,0,-1,-1,-1,0,1,2,2,2,1,1],
  [-1,0,0,0,0,0,-1,0,0,0,0,-1,0,0,0,0,1,1,1,1],
  [-1,-1,-1,0,1,1,1,1],
  [-1,-1,-1,1,1,1,1,1],
  [1,-1,1,-1,1],
  [1,0,0,0,0,-1,1,0,0,0,1],
  [-1,0,1,0,-1,0,0,0,0,0,0,0,0,1,0,0,0,1],
  [0,0,1]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hints : Array Hint := #[
  .positive 1 [(0,false,1)],
  .positive 1 [(1,false,1)],
  .positive 1 [(2,true,1)],
  .positive 1 [],
  .positive 1 [(2,true,1),(3,false,1)],
  .positive 1 [(5,false,1)],
  .positive 1 [(6,false,1)],
  .positive 1 [(6,false,1),(4,true,1)],
  .positive 1 [(1,false,1),(7,false,1),(8,false,1),(9,false,1),(10,false,1),(11,false,1)],
  .root 4 12,
  .positive 1 [(4,false,1)],
  .positive 1 [(13,false,1)],
  .positive 1 [(1,false,3),(14,false,1)],
  .positive 1 [(1,false,2),(14,false,1),(6,false,1),(15,true,1)],
  .positive 1 [(1,false,1),(7,false,1)],
  .positive 1 [(2,true,1),(7,false,1)],
  .positive 1 [(7,false,1)],
  .positive 1 [(2,true,1),(9,false,1),(10,false,1),(16,false,1),(7,false,3)],
  .positive 1 [(17,false,1)],
  .positive 1 [(7,false,1),(8,false,1),(18,false,1),(11,false,1),(19,true,1),(6,false,1)],
  .positive 1 [(1,false,2)],
  .positive 1 [(10,false,1),(20,false,1)],
  .positive 1 [(7,false,1),(21,false,1)],
  .positive 1 [(1,false,1),(7,false,1),(22,true,1),(21,false,1)],
  .positive 1 [(1,false,2),(14,false,1),(23,false,1)],
  .positive 1 [(7,false,1),(8,false,1),(11,false,1),(18,false,1),(19,false,1)],
  .root 22 1,
  .positive 1 [(1,false,1),(22,false,1)],
  .positive 1 [(24,false,1)],
  .positive 1 [(1,false,4),(7,false,1),(8,false,1)],
  .positive 1 [(1,false,3),(7,false,1),(8,false,1),(6,false,1),(25,true,1)],
  .positive 1 [(26,false,1)],
  .positive 1 [(27,false,1)],
  .positive 1 [(1,false,2),(7,false,1),(9,false,1),(10,false,1)],
  .positive 1 [(1,false,1),(7,false,1),(9,false,1),(10,false,1),(28,true,1)],
  .positive 1 [(1,false,1),(10,false,1),(29,false,1)],
  .positive 1 [(7,false,1),(30,true,1),(21,false,1)],
  .positive 1 [(1,false,1),(10,false,1)],
  .positive 1 [(2,true,1),(10,false,1)],
  .positive 1 [(10,false,1)],
  .positive 1 [(2,true,1),(10,false,1),(31,false,1)],
  .positive 1 [(32,false,1)],
  .positive 1 [(6,false,1),(33,true,1)],
  .positive 1 [(7,false,1),(19,false,1)],
  .positive 1 [(7,false,1),(34,true,1)],
  .positive 1 [(1,false,3)],
  .positive 1 [(1,false,2),(7,false,1),(35,true,1)],
  .positive 1 [(37,false,1)],
  .positive 1 [(38,false,1)],
  .positive 1 [(1,false,2),(38,false,1),(36,true,1)],
  .positive 1 [(1,false,3),(8,false,1),(39,false,1),(40,false,1),(7,false,2)],
  .positive 1 [(33,false,1)],
  .positive 1 [(1,false,1),(7,false,1),(41,false,1),(8,false,1)],
  .root 36 42,
  .positive 1 [(1,false,2),(36,false,1)]]
end GeometricMaxCut.FinitePoly.F8


namespace GeometricMaxCut.FinitePoly.F8
open GeometricMaxCut FinitePoly Certificate

def tree0 : Tree := (.leaf 0 0 [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 8 [false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree0 (by decide +kernel)

def tree1 : Tree := (.leaf 2 2 [0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 8 [true,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree1 (by decide +kernel)

def tree2 : Tree := (.leaf 0 2 [0,1,2,3,4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 8 [false,true,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree2 (by decide +kernel)

def tree3 : Tree := (.signs 4 (.leaf 2 3 [0,0,1,5,6,7]) (.leaf 4 4 [8,9]) (.leaf 4 4 [8,10]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w3 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 8 [true,true,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree3 (by decide +kernel)

def tree6 : Tree := (.bisect (.leaf 2 3 [0,0,11,12,6,13]) (.leaf 0 4 [8,10,14,15,16,17]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w6 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 8 [false,true,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree6 (by decide +kernel)

def tree7 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,14,18,6,19]) (.leaf 4 5 [8,10,8,10,20,21,22,23])) (.signs 22 (.leaf 4 5 [8,10,8,10,20,21,22,23]) (.leaf 6 6 [24,25,26]) (.leaf 6 6 [24,25,27])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w7 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 8 [true,true,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree7 (by decide +kernel)

def tree14 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,28,29,6,30]) (.leaf 4 1 [8,10,31,32,33,34])) (.bisect (.leaf 4 5 [8,10,8,10,31,35,22,36]) (.leaf 0 6 [24,25,27,37,38,39,40])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w14 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 8 [false,true,true,true,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree14 (by decide +kernel)

def tree15 : Tree := (.bisect (.leaf 2 3 [0,0,37,41,6,42]) (.bisect (.bisect (.leaf 2 5 [0,8,10,37,43,5,44]) (.leaf 6 5 [24,25,27,8,10,45,43,21,46])) (.signs 36 (.leaf 6 7 [24,25,27,24,25,27,45,47,48,49]) (.leaf 8 8 [50,51,52,53]) (.leaf 8 8 [50,51,52,54]))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w15 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 8 [true,true,true,true,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree15 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F8


namespace GeometricMaxCut.FinitePoly
open GeometricMaxCut

theorem finite8 (q : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HullAt q 8 := by
  apply hull_succ (n:=7) (lt_of_lt_of_le (by norm_num) ha) (finite7 q ha hq)
  intro b k r hk t
  have hk0 : k ≤ 3 := hk.1
  interval_cases k <;> cases r <;> cases b
  · exact F8.w0 q t ha hq
  · exact F8.w1 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F8.w1 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F8.w0 q (-t) ha hq)
  · exact F8.w2 q t ha hq
  · exact F8.w3 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F8.w3 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F8.w2 q (-t) ha hq)
  · exact F8.w6 q t ha hq
  · exact F8.w7 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F8.w7 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F8.w6 q (-t) ha hq)
  · exact F8.w14 q t ha hq
  · exact F8.w15 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F8.w15 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F8.w14 q (-t) ha hq)

end GeometricMaxCut.FinitePoly


namespace GeometricMaxCut.FinitePoly.F9
open GeometricMaxCut FinitePoly Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def coefficients : Table := #[
  [1,1],
  [1,0,1],
  [1,0,0,0,1],
  [0,1],
  [-1,1],
  [-1,0,1,2,3,4,5,6,6,5,4,3,2,1],
  [-1,1,-1,1,-1,1,-1,1,0,1,0,1,0,1],
  [-1,1,0,1,0,1,0,1],
  [-1,1,1,1,1,1,1,1,1],
  [1,1,1,1,1,1,1],
  [1,-1,1,-1,1,-1,1],
  [-1,1,1],
  [1,0,0,1,1,1,1,1,1],
  [-1,1,1,-1,-1,-1,-1,-1,-1,0,1,1,1,1,1,1,1,1,1,1,1,1],
  [-1,0,1,0,1,0,1,-1,1,0,1,0,1],
  [-1,0,0,1,1,1,1,1,1],
  [-1,-1,0,0,0,0,0,1,1,1,1,1,1,1],
  [1,-2,1,-2,1,-2,1,-1,0,0,0,0,0,0,-1,0,0,1,1,2,3,3,3,2,2,1,1],
  [-1,1,-1,1,-1,1,-1,0,0,0,0,0,0,0,1,0,1,0,1],
  [-1,0,0,1,0,1,0,1],
  [-1,-1,1,1,1,1,1,1,1],
  [1,1,1],
  [1,-1,1],
  [1,0,0,0,0,0,0,1,0,0,0,0,0,1],
  [0,1,1],
  [-1,1,1,1],
  [1,1,1,1,1],
  [-1,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,1],
  [-1,0,1,1],
  [1,0,-1,0,-1,0,-1,-1,0,0,0,0,0,-1,1,0,1,0,0,1,1,1,0,1,0,1],
  [-1,-2,-3,-2,-1,0,1,2,3,3,3,3,3,3,3,4,4,4,4,4,4,4,3,2,1],
  [-1,0,0,1,-1,0,0,1,-1,0,1,1,-1,0,1,0,0,0,1,0,0,0,1],
  [-1,-1,0,0,1,1,1,1,1],
  [1,1,0,-1,-2,-1,-2,-1,-2,-1,-3,-1,-2,0,-1,2,0,3,2,3,2,3,2,3,3,3,4,3,3,2,2,1,1],
  [-1,0,-1,1,0,1,0,1],
  [1,0,1,-2,1,-2,1,-1,1,0,-1,0,-1,0,-1,-1,-1,-1,0,-1,1,-1,3,-1,3,0,3,0,2,0,1],
  [-1,1,-1,1,-1,1,-1,0,0,0,0,0,0,-1,1,-1,1,-1,1,0,1,0,1],
  [-1,0,0,1,0,0,1],
  [1,-1,1,-1,1,-1,0,1,-1,1,-1,1],
  [1,0,-1,0,1],
  [-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1],
  [0,0,1,1],
  [-1,1,1,1,1],
  [-1,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1],
  [-1,1,0,1],
  [-1,0,0,0,1,1,1,1],
  [1,-1,1,-1,0,-1,0,-1,0,-1,0,0,0,0,0,0,0,1,0,1,0,0,1,0,1,0,1,0,1],
  [-1,0,0,1,1],
  [-1,0,0,0,1,0,1],
  [1,0,0,0,-1,0,-1,0,0,-1,0,0,0,0,0,-1,0,0,0,0,0,0,1,0,1,0,1,0,1],
  [-1,0,0,0,1,0,-1,0,1,-1,1,0,0,-1,1,0,1,-1,0,0,1],
  [-1,0,0,0,0,1,1,1,1],
  [1,-1,-1,-1,-1,-1,-1,0,-1,0,0,0,0,1,0,0,0,0,1,0,0,0,1],
  [1],
  [-1,-1,-1,-1,-1,1,1,1,1,0,0,0,1,1,1,1,0,0,1,1,1,1,0,1,1,1,1,1,1,1,1],
  [-1,-1,0,1,1,1],
  [1,0,-1,0,-1,0,-1,0,-1,0,-1,-1,0,0,0,0,1,-1,2,0,1,0,0,1,1,1,-1,2,0,2,0,1,0,1],
  [-1,-1,-1,0,0,1,1,1,1],
  [1,1,2,-1,0,-3,0,-2,1,0,0,-1,-2,-1,-2,-1,-3,-2,-3,-1,-1,0,0,1,2,1,2,1,2,3,3,3,2,2,1,1],
  [1,2,3,4,6,6,6,7,9,10,11,13,14,14,14,14,14,13,11,9,8,6,5,3,2,1,1]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hints : Array Hint := #[
  .positive 1 [(0,false,1),(1,false,1),(2,false,1)],
  .positive 1 [(3,false,1)],
  .positive 1 [(4,true,1)],
  .positive 1 [],
  .positive 1 [(4,true,1),(5,false,1)],
  .positive 1 [(0,false,1),(7,false,1)],
  .positive 1 [(8,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(6,true,1)],
  .positive 1 [(3,false,1),(0,false,1),(9,false,1),(10,false,1)],
  .root 6 0,
  .positive 1 [(0,false,1),(6,false,1)],
  .positive 1 [(11,false,1)],
  .positive 1 [(12,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(1,false,1),(2,false,1)],
  .positive 1 [(13,true,1),(0,false,1),(1,false,1),(2,false,1)],
  .positive 1 [(3,false,1),(0,false,1)],
  .positive 1 [(4,true,1),(0,false,1)],
  .positive 1 [(0,false,1)],
  .positive 1 [(4,true,1),(9,false,1),(14,false,1),(0,false,2)],
  .positive 1 [(15,false,1)],
  .positive 1 [(0,false,1),(16,true,1),(10,false,1),(8,false,1)],
  .positive 1 [(3,false,2)],
  .positive 1 [(3,false,1),(0,false,1),(17,true,1)],
  .positive 1 [(0,false,1),(19,false,1)],
  .positive 1 [(20,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(18,true,1),(20,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(21,false,1),(22,false,1),(23,false,1)],
  .positive 1 [(0,false,1),(16,false,1),(10,false,1)],
  .root 18 24,
  .positive 1 [(3,false,1),(0,false,1),(18,false,1)],
  .positive 1 [(25,false,1)],
  .positive 1 [(3,false,4),(26,false,1)],
  .positive 1 [(3,false,3),(26,false,1),(8,false,1),(27,true,1)],
  .positive 1 [(28,false,1)],
  .positive 1 [(3,false,3),(0,false,1),(26,false,1),(29,true,1)],
  .positive 1 [(3,false,1),(21,false,1)],
  .positive 1 [(4,true,1),(21,false,1)],
  .positive 1 [(21,false,1)],
  .positive 1 [(4,true,1),(21,false,1),(30,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(22,false,1),(28,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(1,false,1),(31,true,1)],
  .positive 1 [(32,false,1)],
  .positive 1 [(0,false,1),(33,true,1)],
  .positive 1 [(0,false,1),(3,false,2)],
  .positive 1 [(0,false,1),(34,false,1)],
  .positive 1 [(3,false,1),(35,true,1),(0,false,2)],
  .positive 1 [(3,false,3)],
  .positive 1 [(21,false,1),(37,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(21,false,1),(37,false,1),(36,true,1)],
  .positive 1 [(3,false,3),(0,false,1),(1,false,1),(26,false,1),(38,false,1),(39,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(31,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(40,false,1)],
  .root 36 41,
  .positive 1 [(3,false,2),(0,false,1),(36,false,1)],
  .positive 1 [(42,false,1)],
  .positive 1 [(3,false,5),(0,false,1),(1,false,1)],
  .positive 1 [(3,false,4),(43,true,1),(0,false,1),(1,false,1),(8,false,1)],
  .positive 1 [(0,false,1),(44,false,1)],
  .positive 1 [(3,false,1),(45,false,1)],
  .positive 1 [(0,false,1),(20,false,1),(46,true,1)],
  .positive 1 [(47,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(48,false,1)],
  .positive 1 [(49,true,1),(0,false,1),(21,false,1),(37,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(1,false,1)],
  .positive 1 [(0,false,1),(4,true,1),(1,false,1)],
  .positive 1 [(0,false,1),(1,false,1)],
  .positive 1 [(4,true,1),(22,false,1),(21,false,1),(50,false,1),(1,false,2),(0,false,3)],
  .positive 1 [(51,true,1)],
  .positive 1 [(3,false,4),(0,false,1),(1,false,1),(52,true,1)],
  .positive 1 [(26,false,1)],
  .root 51 53,
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(54,true,1)],
  .positive 1 [(51,false,1)],
  .positive 1 [(0,false,1),(22,false,1),(55,false,1)],
  .positive 1 [(1,false,1),(56,true,1),(0,false,2)],
  .positive 1 [(3,false,2),(21,false,1)],
  .positive 1 [(57,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(58,true,1)],
  .positive 1 [(0,false,1),(4,true,1),(1,false,1),(26,false,1)],
  .positive 1 [(3,false,1),(1,false,1),(59,false,1),(4,true,2),(0,false,2)]]
end GeometricMaxCut.FinitePoly.F9


namespace GeometricMaxCut.FinitePoly.F9
open GeometricMaxCut FinitePoly Certificate

def tree0 : Tree := (.leaf 0 0 [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [false,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree0 (by decide +kernel)

def tree1 : Tree := (.leaf 2 2 [0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [true,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree1 (by decide +kernel)

def tree2 : Tree := (.leaf 0 2 [0,1,2,3,4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [false,true,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree2 (by decide +kernel)

def tree3 : Tree := (.signs 6 (.leaf 2 3 [0,0,1,5,6,7]) (.leaf 4 4 [8,9]) (.leaf 4 4 [8,10]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w3 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [true,true,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree3 (by decide +kernel)

def tree6 : Tree := (.bisect (.leaf 2 1 [0,11,12,13,14]) (.leaf 0 4 [8,10,15,16,17,18]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w6 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [false,true,true,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree6 (by decide +kernel)

def tree7 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,15,19,6,20]) (.leaf 4 3 [8,10,0,21,19,5,22])) (.signs 18 (.leaf 4 5 [8,10,8,10,21,23,24,25]) (.leaf 6 6 [26,27,28]) (.leaf 6 6 [26,27,29])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w7 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [true,true,true,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree7 (by decide +kernel)

def tree14 : Tree := (.bisect (.leaf 2 3 [0,0,30,31,6,32]) (.bisect (.leaf 4 3 [8,10,0,33,31,5,34]) (.leaf 0 6 [26,27,29,35,36,37,38])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w14 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [false,true,true,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree14 (by decide +kernel)

def tree15 : Tree := (.bisect (.leaf 2 3 [0,0,35,39,6,40]) (.bisect (.bisect (.leaf 2 5 [0,8,10,35,41,5,42]) (.leaf 4 7 [8,10,26,27,29,43,44,23,45])) (.signs 36 (.leaf 6 7 [26,27,29,26,27,29,46,44,47,48]) (.leaf 8 8 [49,50,51,52]) (.leaf 8 8 [49,50,51,53]))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w15 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [true,true,true,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree15 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F9


namespace GeometricMaxCut.FinitePoly.F9
open GeometricMaxCut FinitePoly Certificate

def tree30 : Tree := (.bisect (.leaf 2 3 [0,0,54,55,6,56]) (.bisect (.leaf 4 5 [8,10,8,10,57,58,24,59]) (.bisect (.leaf 6 7 [26,27,29,26,27,29,60,61,47,62]) (.leaf 0 8 [49,50,51,53,63,64,65,66]))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w30 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [false,true,true,true,true,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree30 (by decide +kernel)

def tree31 : Tree := (.bisect (.signs 51 (.leaf 3 1 [0,67,55,3,68]) (.leaf 0 3 [0,69,70,13,71]) (.leaf 0 3 [0,69,72,13,71])) (.bisect (.leaf 2 5 [0,8,10,63,73,5,74]) (.bisect (.leaf 4 7 [8,10,26,27,29,75,76,23,77]) (.leaf 9 5 [49,50,51,53,8,10,78,73,43,79]))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w31 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 9 [true,true,true,true,true,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree31 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F9


namespace GeometricMaxCut.FinitePoly
open GeometricMaxCut

theorem finite9 (q : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HullAt q 9 := by
  apply hull_succ (n:=8) (lt_of_lt_of_le (by norm_num) ha) (finite8 q ha hq)
  intro b k r hk t
  have hk0 : k ≤ 4 := hk.1
  interval_cases k <;> cases r <;> cases b
  · exact F9.w0 q t ha hq
  · exact F9.w1 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F9.w1 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F9.w0 q (-t) ha hq)
  · exact F9.w2 q t ha hq
  · exact F9.w3 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F9.w3 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F9.w2 q (-t) ha hq)
  · exact F9.w6 q t ha hq
  · exact F9.w7 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F9.w7 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F9.w6 q (-t) ha hq)
  · exact F9.w14 q t ha hq
  · exact F9.w15 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F9.w15 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F9.w14 q (-t) ha hq)
  · exact F9.w30 q t ha hq
  · exact F9.w31 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F9.w31 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F9.w30 q (-t) ha hq)

end GeometricMaxCut.FinitePoly


namespace GeometricMaxCut.FinitePoly.F10
open GeometricMaxCut FinitePoly Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def coefficients : Table := #[
  [1,1,1],
  [1,0,0,1,0,0,1],
  [0,1],
  [-1,1],
  [-1,0,1,2,3,4,5,6,7,7,6,5,4,3,2,1],
  [-1,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1],
  [-1,0,1,1,1,1,1,1,1,1],
  [-1,1,1,1,1,1,1,1,1,1],
  [1,1],
  [1,0,1],
  [1,0,0,0,1],
  [1,0,0,0,0,0,0,0,1],
  [1],
  [-1,1,1],
  [1,-1,1],
  [1,0,0,0,1,1,1],
  [-1,2,-1,0,-1,0,-1,0,-1,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1],
  [-1,0,1,0,1,0,1,0,0,0,1,0,1,0,1],
  [-1,1,1,-1,0,1],
  [-1,0,0,0,0,0,0,0,1,0,1,0,1,0,1],
  [1,-1,-1,-1,-1,-1,-1,-1,0,-1,0,0,0,0,0,0,-1,-1,0,1,2,3,4,6,7,7,6,5,4,3,2,1],
  [-1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,1,1,1,1,1,1,1],
  [-1,-1,0,1,1,1,1,1,1,1],
  [-1,0,1,0,1,0,1,0,1],
  [1,1,1,1,1,1,1],
  [1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1],
  [-1,1,1,1],
  [-1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,1,0,-1,0,1],
  [-1,0,1,1],
  [1,1,-1,-1,-1,-1,-1,-1,-2,-1,0,0,0,0,0,-1,0,1,1,1,1,0,1,2,2,1,1,1,1,1,1],
  [-1,-2,-3,-2,-1,0,1,2,3,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,4,3,2,1],
  [-1,0,0,0,1,1,1,1,1,1],
  [-1,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,1],
  [-1,0,1,0,0,0,1],
  [-1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1],
  [1,0,-1,0,-1,0,-1,0,0,0,-1,0,-1,0,-1,1,-1,0,0,0,0,0,-1,-1,-1,0,0,1,2,3,3,3,2,2,1,1],
  [-1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,1,1,1,1,1,1],
  [-1,0,0,0,1,0,0,1],
  [-1,-1,-1,1,1,1,1,1,1,1],
  [1,-1,1,-1,1,-1,1],
  [1,0,0,0,0,0,0,-1,1,0,0,0,0,0,1],
  [0,0,1],
  [-1,1,1,1,1],
  [1,1,1,1,1],
  [-1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,1],
  [-1,1,0,1],
  [1,-1,0,0,-1,0,0,0,1,-1,0,0,0,0,0,0,1,-1,0,1,0,0,0,0,0,0,0,1],
  [-1,0,0,1,1],
  [-1,-1,0,0,1,1,1,1,1],
  [1,1,0,0,-1,-1,-1,-1,-1,0,-1,-1,0,0,0,0,0,-1,-1,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1],
  [-1,0,-1,0,1,0,1,-1,1,-1,0,1,0,1,-1,1,-1,1,0,1,0,0,0,0,1,0,1],
  [-1,0,0,0,0,1,1,1,1,1],
  [-1,0,0,0,0,0,0,1,0,0,0,0,1,0,-1,0,1,-1,0,0,1,0,0,0,1],
  [-1,-1,0,0,0,1,1,1,1,1],
  [-1,-1,-1,0,0,0,0,0,-1,-1,-1,0,0,0,0,0,0,0,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1],
  [-1,-1,0,1,0,0,1,1],
  [1,2,3,1,-1,-3,-3,-3,-2,-1,1,0,-1,-3,-3,-3,-3,-3,-4,-5,-5,-4,-3,-1,0,1,2,4,4,4,4,4,4,5,6,7,7,6,5,4,3,2,1],
  [-1,-1,-1,-1,0,1,1,1,1,1],
  [1,1,2,1,0,-1,-2,-1,-1,0,1,1,0,-1,-2,-1,-2,-1,-2,-2,-2,-3,-1,-1,0,-1,1,-1,1,-1,1,0,2,2,3,3,3,3,2,2,1,1],
  [-1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,-1,0,0,0,0,0,1,1,1,1,1],
  [-1,0,-1,0,1,0,1,0,1],
  [1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,1],
  [-1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1],
  [0,0,0,1]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hints : Array Hint := #[
  .positive 1 [(0,false,1),(1,false,1)],
  .positive 1 [(2,false,1)],
  .positive 1 [(3,true,1)],
  .positive 1 [],
  .positive 1 [(3,true,1),(4,false,1)],
  .positive 1 [(6,false,1)],
  .positive 1 [(7,false,1)],
  .positive 1 [(7,false,1),(5,true,1)],
  .positive 1 [(2,false,1),(8,false,1),(9,false,1),(10,false,1),(11,false,1)],
  .root 5 12,
  .positive 1 [(5,false,1)],
  .positive 1 [(13,false,1)],
  .positive 1 [(8,false,1),(14,false,1),(15,false,1)],
  .positive 1 [(2,false,1),(0,false,1),(1,false,1)],
  .positive 1 [(16,true,1),(8,false,1),(0,false,1),(1,false,1)],
  .positive 1 [(2,false,1),(8,false,1)],
  .positive 1 [(3,true,1),(8,false,1)],
  .positive 1 [(8,false,1)],
  .positive 1 [(3,true,1),(9,false,1),(10,false,1),(17,false,1),(8,false,3)],
  .positive 1 [(0,false,1),(18,false,1),(9,false,1)],
  .positive 1 [(7,false,1),(8,false,1),(11,false,1),(19,true,1)],
  .positive 1 [(2,false,2)],
  .positive 1 [(2,false,1),(20,true,1)],
  .positive 1 [(22,false,1)],
  .positive 1 [(8,false,1),(23,false,1)],
  .positive 1 [(2,false,1),(8,false,1),(21,true,1),(23,false,1)],
  .positive 1 [(2,false,2),(24,false,1),(25,false,1)],
  .positive 1 [(8,false,1),(11,false,1),(19,false,1)],
  .root 21 2,
  .positive 1 [(2,false,1),(21,false,1)],
  .positive 1 [(26,false,1)],
  .positive 1 [(2,false,4),(8,false,1),(14,false,1),(0,false,1)],
  .positive 1 [(2,false,3),(8,false,1),(9,false,1),(14,false,1),(0,false,1),(7,false,1),(27,true,1)],
  .positive 1 [(28,false,1)],
  .positive 1 [(2,false,3),(8,false,1),(14,false,1),(0,false,1),(29,true,1)],
  .positive 1 [(2,false,1),(0,false,1)],
  .positive 1 [(3,true,1),(0,false,1)],
  .positive 1 [(0,false,1)],
  .positive 1 [(3,true,1),(0,false,1),(30,false,1)],
  .positive 1 [(31,false,1)],
  .positive 1 [(0,false,1),(7,false,1),(32,true,1)],
  .positive 1 [(8,false,1),(2,false,2)],
  .positive 1 [(8,false,1),(9,false,1),(33,false,1)],
  .positive 1 [(2,false,1),(23,false,1),(34,true,1),(8,false,2)],
  .positive 1 [(2,false,3)],
  .positive 1 [(2,false,2),(8,false,1),(35,true,1)],
  .positive 1 [(0,false,1),(37,false,1)],
  .positive 1 [(38,false,1)],
  .positive 1 [(2,false,2),(38,false,1),(36,true,1)],
  .positive 1 [(2,false,3),(0,false,1),(14,false,1),(39,false,1),(40,false,1),(8,false,2)],
  .positive 1 [(0,false,1),(32,false,1)],
  .positive 1 [(2,false,1),(8,false,1),(34,false,1)],
  .root 36 41,
  .positive 1 [(2,false,2),(36,false,1)],
  .positive 1 [(42,false,1)],
  .positive 1 [(2,false,5),(43,false,1)],
  .positive 1 [(2,false,4),(43,false,1),(44,true,1),(7,false,1)],
  .positive 1 [(8,false,1),(45,false,1)],
  .positive 1 [(2,false,1),(8,false,1),(9,false,1),(14,false,1),(28,false,1)],
  .positive 1 [(9,false,1),(10,false,1),(46,true,1),(23,false,1),(8,false,2)],
  .positive 1 [(47,false,1)],
  .positive 1 [(2,false,1),(48,false,1)],
  .positive 1 [(49,true,1),(38,false,1)],
  .positive 1 [(2,false,1),(8,false,1),(9,false,1)],
  .positive 1 [(8,false,1),(3,true,1),(9,false,1)],
  .positive 1 [(8,false,1),(9,false,1)],
  .positive 1 [(3,true,1),(9,false,1),(24,false,1),(50,false,1),(8,false,2)],
  .positive 1 [(51,false,1)],
  .positive 1 [(9,false,1),(39,false,1),(7,false,1),(52,true,1),(8,false,2)],
  .positive 1 [(2,false,2),(0,false,1)],
  .positive 1 [(53,false,1)],
  .positive 1 [(2,false,1),(8,false,1),(54,true,1),(23,false,1)],
  .positive 1 [(9,false,1),(55,false,1)],
  .positive 1 [(2,false,1),(56,true,1)],
  .positive 1 [(57,false,1)],
  .positive 1 [(2,false,1),(8,false,1),(58,true,1)],
  .positive 1 [(2,false,4)],
  .positive 1 [(8,false,1),(60,false,1)],
  .positive 1 [(2,false,3),(8,false,1),(60,false,1),(59,true,1)],
  .positive 1 [(2,false,4),(43,false,1),(61,false,1)],
  .positive 1 [(9,false,1),(39,false,1),(52,false,1),(8,false,2)],
  .positive 1 [(2,false,1),(54,false,1)],
  .positive 1 [(2,false,2),(62,false,1),(8,false,1)],
  .root 59 63,
  .positive 1 [(2,false,3),(59,false,1)]]
end GeometricMaxCut.FinitePoly.F10


namespace GeometricMaxCut.FinitePoly.F10
open GeometricMaxCut FinitePoly Certificate

def tree0 : Tree := (.leaf 0 0 [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [false,false,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree0 (by decide +kernel)

def tree1 : Tree := (.leaf 2 2 [0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [true,false,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree1 (by decide +kernel)

def tree2 : Tree := (.leaf 0 2 [0,1,2,3,4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [false,true,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree2 (by decide +kernel)

def tree3 : Tree := (.signs 5 (.leaf 2 3 [0,0,1,5,6,7]) (.leaf 4 4 [8,9]) (.leaf 4 4 [8,10]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w3 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [true,true,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree3 (by decide +kernel)

def tree6 : Tree := (.bisect (.leaf 2 1 [0,11,12,13,14]) (.leaf 0 4 [8,10,15,16,17,18]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w6 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [false,true,true,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree6 (by decide +kernel)

def tree7 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,15,19,6,20]) (.leaf 4 3 [8,10,0,21,19,5,22])) (.signs 21 (.leaf 4 5 [8,10,8,10,21,23,24,25]) (.leaf 6 6 [26,27,28]) (.leaf 6 6 [26,27,29])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w7 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [true,true,true,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree7 (by decide +kernel)

def tree14 : Tree := (.bisect (.leaf 2 3 [0,0,30,31,6,32]) (.bisect (.leaf 4 3 [8,10,0,33,31,5,34]) (.leaf 0 6 [26,27,29,35,36,37,38])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w14 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [false,true,true,true,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree14 (by decide +kernel)

def tree15 : Tree := (.bisect (.leaf 2 3 [0,0,35,39,6,40]) (.bisect (.bisect (.leaf 4 5 [8,10,8,10,41,42,24,43]) (.leaf 6 5 [26,27,29,8,10,44,42,23,45])) (.signs 36 (.leaf 6 7 [26,27,29,26,27,29,44,46,47,48]) (.leaf 8 8 [49,50,51,52]) (.leaf 8 8 [49,50,51,53]))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w15 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [true,true,true,true,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree15 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F10


namespace GeometricMaxCut.FinitePoly.F10
open GeometricMaxCut FinitePoly Certificate

def tree30 : Tree := (.bisect (.leaf 2 3 [0,0,54,55,6,56]) (.bisect (.leaf 4 5 [8,10,8,10,57,58,24,59]) (.bisect (.leaf 6 7 [26,27,29,26,27,29,60,61,47,62]) (.leaf 0 8 [49,50,51,53,63,64,65,66]))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w30 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [false,true,true,true,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree30 (by decide +kernel)

def tree31 : Tree := (.bisect (.leaf 2 3 [0,0,63,67,6,68]) (.bisect (.leaf 4 5 [8,10,8,10,69,70,24,71]) (.bisect (.bisect (.leaf 4 7 [8,10,26,27,29,69,72,23,73]) (.leaf 4 9 [8,10,49,50,51,53,69,74,42,75])) (.signs 59 (.leaf 8 9 [49,50,51,53,49,50,51,53,76,74,77,78]) (.leaf 10 10 [79,80,81,82,83]) (.leaf 10 10 [79,80,81,82,84])))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w31 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 10 [true,true,true,true,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree31 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F10


namespace GeometricMaxCut.FinitePoly
open GeometricMaxCut

theorem finite10 (q : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HullAt q 10 := by
  apply hull_succ (n:=9) (lt_of_lt_of_le (by norm_num) ha) (finite9 q ha hq)
  intro b k r hk t
  have hk0 : k ≤ 4 := hk.1
  interval_cases k <;> cases r <;> cases b
  · exact F10.w0 q t ha hq
  · exact F10.w1 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F10.w1 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F10.w0 q (-t) ha hq)
  · exact F10.w2 q t ha hq
  · exact F10.w3 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F10.w3 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F10.w2 q (-t) ha hq)
  · exact F10.w6 q t ha hq
  · exact F10.w7 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F10.w7 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F10.w6 q (-t) ha hq)
  · exact F10.w14 q t ha hq
  · exact F10.w15 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F10.w15 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F10.w14 q (-t) ha hq)
  · exact F10.w30 q t ha hq
  · exact F10.w31 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F10.w31 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F10.w30 q (-t) ha hq)

end GeometricMaxCut.FinitePoly


namespace GeometricMaxCut.FinitePoly.F11
open GeometricMaxCut FinitePoly Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def coefficients : Table := #[
  [1,1],
  [1,1,1,1,1],
  [1,-1,1,-1,1],
  [0,1],
  [-1,1],
  [-1,0,1,2,3,4,5,6,7,8,8,7,6,5,4,3,2,1],
  [-1,1,-1,1,-1,1,-1,1,-1,1,0,1,0,1,0,1,0,1],
  [-1,1,0,1,0,1,0,1,0,1],
  [-1,1,1,1,1,1,1,1,1,1,1],
  [1,-1,1],
  [1,1,1],
  [1,0,0,1,0,0,1],
  [1,0,0,-1,0,0,1],
  [-1,1,1],
  [1,0,0,1,1,1,1,1,1,1,1],
  [-1,1,1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [-1,0,1,0,1,0,1,0,1,-1,1,0,1,0,1,0,1],
  [-1,0,0,1,1,1,1,1,1,1,1],
  [-1,-1,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1],
  [1,-2,1,-2,1,-2,1,-2,1,-1,0,0,0,0,0,0,0,0,-1,0,0,1,1,2,2,3,4,4,4,3,3,2,2,1,1],
  [-1,1,-1,1,-1,1,-1,1,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1],
  [-1,1,0,0,0,1,-1,1],
  [-1,-1,1,1,1,1,1,1,1,1,1],
  [1,0,1],
  [1,0,0,0,1],
  [1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1],
  [0,1,1],
  [-1,1,1,1],
  [1,1,1,1,1,1,1],
  [-1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1],
  [-1,0,1,1],
  [1,0,0,0,1,1,1,1,1,1,1],
  [-1,1,1,1,-1,-1,-1,-1,-1,-2,-1,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  [-1,-2,-3,-2,-1,0,1,2,3,4,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,5,4,3,2,1],
  [-1,1,-1,1,0,1,0,1,0,1],
  [-1,0,-1,1,-1,1,-1,1,-1,1,-1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1],
  [1,-2,1,-2,1,-2,1,-2,1,-1,0,0,0,0,0,0,0,0,0,-1,1,-1,2,-1,3,-1,4,-1,5,-1,5,-1,5,0,4,0,3,0,2,0,1],
  [-1,-1,0,0,1,1,1,1,1,1,1],
  [1,0,-1,0,-1,0,-1,0,-1,1,-1,0,-1,0,-1,0,-1,1,-1,0,0,0,0,0,0,-1,-1,-1,0,0,1,1,3,3,4,3,3,2,2,1,1],
  [-1,1,-1,1,-1,1,-1,1,-1,0,0,0,0,0,0,0,0,-1,1,-1,1,-1,1,-1,1,0,1,0,1,0,1],
  [-1,0,0,1,0,0,0,1],
  [-1,-1,-1,1,1,1,1,1,1,1,1],
  [1,-1,1,-1,1,-1,1,-1,0,1,-1,1,-1,1,-1,1],
  [1,0,0,0,0,0,0,0,1],
  [-1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1],
  [0,0,1,1],
  [-1,1,1,1,1],
  [-1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,1],
  [-1,1,0,1],
  [1,0,-1,0,-1,0,-1,0,-1,-1,0,0,0,0,0,0,0,-1,1,0,1,0,1,0,0,1,1,1,0,1,-1,2,0,2,0,1,0,1,0,1],
  [-1,0,0,1,1],
  [-1,0,0,0,1,1,1,1,1,1],
  [-1,0,-1,2,0,3,1,2,0,1,-1,-2,-2,-4,-4,-3,-3,-2,-2,-1,0,-2,0,-1,0,-1,0,0,-1,-1,-1,0,0,1,1,2,2,3,3,3,4,4,4,3,3,2,2,1,1],
  [-1,0,0,0,1,0,0,0,0,0,0,-1,2,0,0,-1,1,0,0,-1,2,0,0,-1,1,0,0,0,1],
  [-1,1,0,0,0,0,1],
  [-1,0,-1,0,0,0,0,0,1,0,1,0,0,1,0,1,-1,1,-1,0,0,0,0,0,1,0,1,0,1,0,1],
  [-1,0,0,0,0,1,0,1,0,1],
  [-1,0,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,1],
  [-1,0,0,0,0,1,0,0,1],
  [1,0,1,-2,1,-2,1,-2,1,-1,1,0,-1,0,-1,0,-1,0,-1,0,-2,0,-1,0,-1,1,0,0,1,1,1,0,2,0,1,1,1,1,1,2,1,1,1,1,0,1],
  [-1,0,-1,0,0,1,0,1,0,1],
  [1,0,1,0,-1,0,-1,0,-1,1,-1,2,-1,0,-1,0,-1,1,-1,1,0,-1,0,-1,0,-1,-1,-1,-2,0,-2,1,-2,2,-2,4,-2,4,-1,4,0,3,0,2,0,1],
  [-1,1,-1,1,-1,1,-1,1,-1,0,0,0,0,0,0,0,0,-1,1,-1,1,-1,1,-1,0,0,0,0,0,0,0,1,0,1,0,1],
  [-1,-1,-1,-1,1,1,1,1,1,1,1],
  [1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,1],
  [-1,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1],
  [0,0,0,1,1],
  [-1,1,1,1,1,1],
  [-1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,1],
  [-1,0,1,1,1,1],
  [-1,0,0,0,0,1,1,1,1,1],
  [1,0,0,0,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,0,0,0,0,0,0,0,1,1,1,1,1,0,0,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1],
  [-1,-1,0,0,0,1,1,1,1,1],
  [1,0,-2,1,2,-3,-1,3,-1,-2,2,-1,-1,2,-1,-1,2,-1,-1,1,-1,0,2,-2,-1,3,-1,-2,2,1,-1,0,0,1,0,-1,1,1,-1,0,1],
  [-1,0,0,0,1,1],
  [-1,-1,0,1,0,0,1,1],
  [1,1,1,0,0,-1,-1,-1,-1,-1,0,0,-1,-1,0,0,0,0,0,0,-1,-1,0,0,0,0,0,-1,-1,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1],
  [-1,-2,-3,-4,-5,-4,-3,-2,-1,0,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,4,4,4,4,4,4,4,3,2,1],
  [-1,1,-1,1,-1,1,0,1,0,1],
  [1,-2,1,-2,1,-2,1,-2,1,-1,0,0,0,0,0,0,0,1,-1,1,-1,1,-1,1,0,0,0,0,0,0,1,-1,1,-1,1],
  [-1,0,-1,0,-1,0,1,0,1,0,1,-1,1,-1,1,0,1,0,1,0,0,0,0,1,0,1,0,1,-1,1,0,1,0,1,0,0,1,0,1,0,1,0,1,0,1],
  [-1,0,1,-1,0,1,0,0,1],
  [1,0,-1,0,-1,0,-1,0,-1,0,-1,0,-1,0,-2,1,-1,1,-1,1,0,1,-1,2,0,1,0,1,0,0,1,1,1,0,1,-1,2,0,2,0,0,1,1,1,1,1,0,1,0,1],
  [-1,0,-1,1,-1,1,0,1,0,1],
  [1,0,1,-2,1,-2,1,-2,1,-1,1,0,-1,0,-1,0,-1,0,-1,0,-1,-1,-1,0,0,-1,1,0,1,-2,3,0,1,-1,2,0,0,1,1,1,-1,2,0,2,0,2,0,1,0,1],
  [-1,-1,-1,-1,0,0,1,1,1,1,1],
  [1,1,2,1,0,-1,-2,-1,-2,0,-1,2,0,1,-2,-1,-2,0,-1,1,0,0,-1,-2,-1,-2,-1,-3,-2,-4,-2,-3,0,-2,1,-1,2,1,2,1,2,1,2,3,3,4,3,3,2,2,1,1],
  [-1,-1,-2,-2,-3,-3,-2,-2,-1,-2,-1,-3,-2,-4,-3,-3,-2,-3,-2,-3,-3,-4,-4,-3,-3,-2,-1,0,1,1,4,3,6,4,7,3,7,3,6,2,4,1,2,0,1]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hints : Array Hint := #[
  .positive 1 [(0,false,1),(1,false,1),(2,false,1)],
  .positive 1 [(3,false,1)],
  .positive 1 [(4,true,1)],
  .positive 1 [],
  .positive 1 [(4,true,1),(5,false,1)],
  .positive 1 [(0,false,1),(7,false,1)],
  .positive 1 [(8,false,1)],
  .positive 1 [(6,true,1),(0,false,1),(8,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(9,false,1),(10,false,1),(11,false,1),(12,false,1)],
  .root 6 0,
  .positive 1 [(0,false,1),(6,false,1)],
  .positive 1 [(13,false,1)],
  .positive 1 [(14,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(1,false,1),(2,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(2,false,1),(15,true,1)],
  .positive 1 [(3,false,1),(0,false,1)],
  .positive 1 [(4,true,1),(0,false,1)],
  .positive 1 [(0,false,1)],
  .positive 1 [(4,true,1),(10,false,1),(11,false,1),(16,false,1),(0,false,2)],
  .positive 1 [(17,false,1)],
  .positive 1 [(18,true,1),(0,false,1),(9,false,1),(12,false,1),(8,false,1)],
  .positive 1 [(3,false,2)],
  .positive 1 [(3,false,1),(0,false,1),(19,true,1)],
  .positive 1 [(0,false,1),(10,false,1),(21,false,1)],
  .positive 1 [(22,false,1)],
  .positive 1 [(3,false,1),(20,true,1),(0,false,1),(22,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(23,false,1),(24,false,1),(25,false,1)],
  .positive 1 [(0,false,1),(9,false,1),(12,false,1),(18,false,1)],
  .root 20 26,
  .positive 1 [(3,false,1),(0,false,1),(20,false,1)],
  .positive 1 [(27,false,1)],
  .positive 1 [(3,false,4),(28,false,1)],
  .positive 1 [(3,false,3),(8,false,1),(28,false,1),(29,true,1)],
  .positive 1 [(30,false,1)],
  .positive 1 [(31,false,1)],
  .positive 1 [(3,false,2),(10,false,1),(11,false,1)],
  .positive 1 [(3,false,1),(10,false,1),(11,false,1),(32,true,1)],
  .positive 1 [(3,false,1),(10,false,1)],
  .positive 1 [(4,true,1),(10,false,1)],
  .positive 1 [(10,false,1)],
  .positive 1 [(4,true,1),(33,false,1),(10,false,1)],
  .positive 1 [(0,false,1),(34,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(35,true,1)],
  .positive 1 [(0,false,1),(3,false,2)],
  .positive 1 [(3,false,1),(36,true,1),(0,false,2)],
  .positive 1 [(3,false,3)],
  .positive 1 [(37,false,1)],
  .positive 1 [(3,false,2),(38,true,1),(0,false,1)],
  .positive 1 [(0,false,1),(23,false,1),(40,false,1)],
  .positive 1 [(41,false,1)],
  .positive 1 [(3,false,2),(39,true,1),(0,false,1),(41,false,1)],
  .positive 1 [(3,false,3),(42,false,1),(0,false,1),(28,false,1),(43,false,1)],
  .positive 1 [(0,false,1),(35,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(44,false,1)],
  .root 39 45,
  .positive 1 [(3,false,2),(0,false,1),(39,false,1)],
  .positive 1 [(46,false,1)],
  .positive 1 [(3,false,5),(0,false,1),(9,false,1),(10,false,1)],
  .positive 1 [(3,false,4),(0,false,1),(9,false,1),(10,false,1),(8,false,1),(47,true,1)],
  .positive 1 [(0,false,1),(48,false,1)],
  .positive 1 [(3,false,4),(49,true,1),(9,false,1),(10,false,1),(0,false,2)],
  .positive 1 [(50,false,1)],
  .positive 1 [(3,false,1),(51,false,1)],
  .positive 1 [(0,false,1),(52,true,1)],
  .positive 1 [(3,false,1),(0,false,1),(23,false,1)],
  .positive 1 [(0,false,1),(4,true,1),(23,false,1)],
  .positive 1 [(0,false,1),(23,false,1)],
  .positive 1 [(4,true,1),(24,false,1),(53,false,1),(0,false,3),(23,false,3)],
  .positive 1 [(1,false,1),(54,false,1)],
  .positive 1 [(0,false,1),(8,false,1),(43,false,1),(55,true,1)],
  .positive 1 [(3,false,2),(10,false,1)],
  .positive 1 [(0,false,1),(56,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(10,false,1),(9,false,1),(22,false,1),(57,true,1)],
  .positive 1 [(10,false,1),(58,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(10,false,1),(59,true,1)],
  .positive 1 [(3,false,3),(0,false,1)],
  .positive 1 [(0,false,1),(60,false,1)],
  .positive 1 [(3,false,2),(61,true,1),(0,false,2)],
  .positive 1 [(3,false,4)],
  .positive 1 [(63,false,1)],
  .positive 1 [(3,false,3),(0,false,1),(63,false,1),(62,true,1)],
  .positive 1 [(3,false,4),(0,false,1),(9,false,1),(10,false,1),(64,false,1)],
  .positive 1 [(0,false,1),(43,false,1),(55,false,1)],
  .positive 1 [(3,false,1),(0,false,1),(9,false,1),(10,false,1),(57,false,1)],
  .positive 1 [(3,false,2),(65,false,1),(0,false,1)],
  .root 62 66,
  .positive 1 [(3,false,3),(62,false,1),(0,false,1)],
  .positive 1 [(67,false,1)],
  .positive 1 [(3,false,6),(1,false,1)],
  .positive 1 [(3,false,5),(1,false,1),(68,true,1),(8,false,1)],
  .positive 1 [(69,false,1)],
  .positive 1 [(3,false,1),(70,false,1)],
  .positive 1 [(22,false,1),(71,true,1)],
  .positive 1 [(23,false,1),(30,false,1)],
  .positive 1 [(3,false,1),(72,false,1)],
  .positive 1 [(23,false,1),(10,false,1),(41,false,1),(73,true,1)],
  .positive 1 [(74,false,1)],
  .positive 1 [(3,false,1),(23,false,1),(75,false,1)],
  .positive 1 [(63,false,1),(76,true,1)],
  .positive 1 [(3,false,1),(1,false,1)],
  .positive 1 [(4,true,1),(1,false,1)],
  .positive 1 [(1,false,1)],
  .positive 1 [(77,false,1),(4,true,1),(1,false,1)],
  .positive 1 [(0,false,1),(78,true,1)],
  .positive 1 [(3,false,5),(0,false,1),(1,false,1),(79,true,1)],
  .positive 1 [(0,false,1),(9,false,1),(10,false,1)],
  .root 78 0,
  .positive 1 [(1,false,1),(2,false,1),(80,true,1),(0,false,2)],
  .positive 1 [(0,false,1),(78,false,1)],
  .positive 1 [(10,false,1),(81,false,1)],
  .positive 1 [(0,false,1),(1,false,1),(82,true,1)],
  .positive 1 [(3,false,2),(0,false,1),(23,false,1)],
  .positive 1 [(0,false,1),(83,false,1)],
  .positive 1 [(3,false,1),(23,false,1),(84,true,1),(0,false,2)],
  .positive 1 [(3,false,3),(10,false,1)],
  .positive 1 [(85,false,1)],
  .positive 1 [(3,false,2),(0,false,1),(86,true,1)],
  .positive 1 [(4,true,1),(0,false,1),(1,false,1),(10,false,1),(9,false,1)],
  .positive 1 [(3,false,2),(4,true,1),(87,true,1),(0,false,2)]]
end GeometricMaxCut.FinitePoly.F11


namespace GeometricMaxCut.FinitePoly.F11
open GeometricMaxCut FinitePoly Certificate

def tree0 : Tree := (.leaf 0 0 [])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [false,false,false,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree0 (by decide +kernel)

def tree1 : Tree := (.leaf 2 2 [0])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [true,false,false,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree1 (by decide +kernel)

def tree2 : Tree := (.leaf 0 2 [0,1,2,3,4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [false,true,false,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree2 (by decide +kernel)

def tree3 : Tree := (.signs 6 (.leaf 2 3 [0,0,1,5,6,7]) (.leaf 4 4 [8,9]) (.leaf 4 4 [8,10]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w3 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [true,true,false,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree3 (by decide +kernel)

def tree6 : Tree := (.bisect (.leaf 2 1 [0,11,12,13,14]) (.leaf 0 4 [8,10,15,16,17,18]))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w6 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [false,true,true,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree6 (by decide +kernel)

def tree7 : Tree := (.bisect (.bisect (.leaf 2 3 [0,0,15,19,6,20]) (.leaf 4 3 [8,10,0,21,19,5,22])) (.signs 20 (.leaf 4 5 [8,10,8,10,21,23,24,25]) (.leaf 6 6 [26,27,28]) (.leaf 6 6 [26,27,29])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w7 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [true,true,true,false,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree7 (by decide +kernel)

def tree14 : Tree := (.bisect (.leaf 2 3 [0,0,30,31,6,32]) (.bisect (.leaf 4 1 [8,10,33,34,35,36]) (.leaf 0 6 [26,27,29,37,38,39,40])))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w14 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [false,true,true,true,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree14 (by decide +kernel)

def tree15 : Tree := (.bisect (.leaf 2 3 [0,0,37,41,6,42]) (.bisect (.bisect (.leaf 4 3 [8,10,0,43,41,5,44]) (.leaf 6 5 [26,27,29,8,10,45,46,23,47])) (.signs 39 (.leaf 6 7 [26,27,29,26,27,29,45,48,49,50]) (.leaf 8 8 [51,52,53,54]) (.leaf 8 8 [51,52,53,55]))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w15 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [true,true,true,true,false,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree15 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F11


namespace GeometricMaxCut.FinitePoly.F11
open GeometricMaxCut FinitePoly Certificate

def tree30 : Tree := (.bisect (.leaf 2 3 [0,0,56,57,6,58]) (.bisect (.leaf 4 3 [8,10,0,59,57,5,60]) (.bisect (.leaf 6 5 [26,27,29,8,10,61,62,23,63]) (.leaf 0 8 [51,52,53,55,64,65,66,67]))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w30 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [false,true,true,true,true,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree30 (by decide +kernel)

def tree31 : Tree := (.bisect (.leaf 2 3 [0,0,64,68,6,69]) (.bisect (.leaf 4 5 [8,10,8,10,70,71,24,72]) (.bisect (.bisect (.leaf 4 7 [8,10,26,27,29,70,73,23,74]) (.leaf 6 9 [26,27,29,51,52,53,55,75,76,48,77])) (.signs 62 (.leaf 8 9 [51,52,53,55,51,52,53,55,78,76,79,80]) (.leaf 10 10 [81,82,83,84,85]) (.leaf 10 10 [81,82,83,84,86])))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w31 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [true,true,true,true,true,false,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree31 (by decide +kernel)

def tree62 : Tree := (.bisect (.leaf 2 3 [0,0,87,88,6,89]) (.bisect (.leaf 4 5 [8,10,8,10,90,91,24,92]) (.bisect (.leaf 6 7 [26,27,29,26,27,29,93,94,49,95]) (.bisect (.leaf 8 9 [51,52,53,55,51,52,53,55,96,97,79,98]) (.leaf 0 10 [81,82,83,84,86,99,100,101,102])))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w62 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [false,true,true,true,true,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree62 (by decide +kernel)

def tree63 : Tree := (.bisect (.signs 78 (.leaf 3 1 [0,103,88,3,104]) (.leaf 0 3 [0,105,106,13,107]) (.leaf 0 3 [0,105,108,13,107])) (.bisect (.leaf 2 5 [0,8,10,99,109,5,110]) (.bisect (.leaf 4 7 [8,10,26,27,29,111,112,23,113]) (.bisect (.leaf 6 9 [26,27,29,51,52,53,55,114,115,48,116]) (.leaf 11 7 [81,82,83,84,86,26,27,29,117,112,75,118])))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w63 (q t : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HasBound q t 11 [true,true,true,true,true,true,false,false,false,false,false] :=
  initial_sound (tab:=coefficients) (hints:=hints) ha hq tree63 (by decide +kernel)

end GeometricMaxCut.FinitePoly.F11


namespace GeometricMaxCut.FinitePoly
open GeometricMaxCut

theorem finite11 (q : ℝ) (ha : (((4/5:ℚ)):ℝ) ≤ q) (hq : q < 1) : HullAt q 11 := by
  apply hull_succ (n:=10) (lt_of_lt_of_le (by norm_num) ha) (finite10 q ha hq)
  intro b k r hk t
  have hk0 : k ≤ 5 := hk.1
  interval_cases k <;> cases r <;> cases b
  · exact F11.w0 q t ha hq
  · exact F11.w1 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F11.w1 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F11.w0 q (-t) ha hq)
  · exact F11.w2 q t ha hq
  · exact F11.w3 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F11.w3 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F11.w2 q (-t) ha hq)
  · exact F11.w6 q t ha hq
  · exact F11.w7 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F11.w7 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F11.w6 q (-t) ha hq)
  · exact F11.w14 q t ha hq
  · exact F11.w15 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F11.w15 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F11.w14 q (-t) ha hq)
  · exact F11.w30 q t ha hq
  · exact F11.w31 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F11.w31 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F11.w30 q (-t) ha hq)
  · exact F11.w62 q t ha hq
  · exact F11.w63 q t ha hq
  · exact hasBound_compl (by decide +kernel) (F11.w63 q (-t) ha hq)
  · exact hasBound_compl (by decide +kernel) (F11.w62 q (-t) ha hq)

end GeometricMaxCut.FinitePoly

namespace GeometricMaxCut

theorem finite_base {q : ℝ} (ha : (4:ℝ)/5 ≤ q) (hq : q < 1)
    {n : ℕ} (hm : 7 ≤ n) (hn : n ≤ 11) : HullAt q n := by
  have ha' : (((4/5:ℚ)):ℝ) ≤ q := by simpa only [Rat.cast_div, Rat.cast_ofNat] using ha
  interval_cases n
  · exact FinitePoly.finite7 q ha' hq
  · exact FinitePoly.finite8 q ha' hq
  · exact FinitePoly.finite9 q ha' hq
  · exact FinitePoly.finite10 q ha' hq
  · exact FinitePoly.finite11 q ha' hq

end GeometricMaxCut

/-- A single isolated cut attains the unrestricted maximum, for every order and ratio
in the conjecture. The positive-field and negative-field hull estimates preserve
all affine scores when a vertex is prepended. -/
theorem OMA.solution : type_of% @OMA.S_arxiv_2603_08876.main :=
  GeometricMaxCut.source_of_induction
    (fun _ hm hn _ ha hq => GeometricMaxCut.finite_base ha hq hm hn)
    (fun _ hn _ ha hq ih => GeometricMaxCut.induction_step hn ha hq ih)
