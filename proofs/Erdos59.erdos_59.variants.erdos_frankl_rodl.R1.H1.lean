import OMAReductions.R_Erdos59_erdos_59_variants_erdos_frankl_rodl_R1
import Mathlib

/-! Rectangle templates and one-sided cut counting for the Erdős–Frankl–Rödl reduction. -/

open Filter Finset SimpleGraph
open scoped Sym2 Classical

noncomputable section

namespace OMA.E59

abbrev V (n : ℕ) := Fin n
abbrev Pair (n : ℕ) := V n × V n
abbrev Rect (n : ℕ) := Finset (V n) × Finset (V n)

variable {n k : ℕ}

def box (r : Rect n) : Finset (Pair n) := r.1 ×ˢ r.2

def region (R : Finset (Rect n)) : Finset (Pair n) := R.biUnion box

def arcs (G : SimpleGraph (V n)) : Finset (Pair n) :=
  univ.filter fun p => G.Adj p.1 p.2

def decode (U S : Finset (Pair n)) : SimpleGraph (V n) :=
  (SimpleGraph.fromRel fun x y => (x,y) ∈ U \ S)ᶜ

-- A menu is the region covered by a fixed-length sequence of rectangles.
def menus (n M : ℕ) := univ.image fun f : Fin M → Rect n => univ.biUnion (box ∘ f)

lemma region_mem {n M : ℕ} {R : Finset (Rect n)} (h : R.card ≤ M) : region R ∈ menus n M := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le h
  let e : Fin (R.card + q) ≃ R ⊕ Fin q := Fintype.equivOfCardEq (by simp)
  let f : R ⊕ Fin q → Rect n := Sum.elim Subtype.val (fun _ => (∅, ∅))
  refine mem_image.mpr ⟨f ∘ e, mem_univ _, ?_⟩
  ext z
  have := e.surjective.exists (p := fun w => z ∈ box (f w))
  simp [region, f, box, Function.comp_def, Sum.exists, Subtype.exists] at this ⊢
  grind

def sparse (n : ℕ) (d : ℝ) : Finset (Finset (Pair n)) :=
  univ.filter fun S => (S.card : ℝ) ≤ d * (n : ℝ)^2

def codes (n M : ℕ) (d : ℝ) := (menus n M) ×ˢ (sparse n d)

def CutLE (d η : ℝ) (T G : SimpleGraph (V n)) : Prop :=
  ∀ r : Rect n, d * ((arcs T ∩ box r).card : ℝ) ≤
    ((arcs G ∩ box r).card : ℝ) + η * (n : ℝ)^2

lemma exists_code (hn : 0 < n) (G : SimpleGraph (V n)) {d η : ℝ}
    (hd : 0 < d) (hd' : d ≤ 1) (hη : 0 < η) :
    ∃ p ∈ codes n ⌈d / η⌉₊ d, G ≤ decode p.1 p.2 ∧ CutLE (d/2) η (decode p.1 p.2) G := by
  let E := arcs G
  let cost := η * (n:ℝ)^2
  -- Adding a rectangle to the maximizer cannot gain more than the charge for that rectangle.
  let score (R : Finset (Rect n)) := d * (region R).card - (E ∩ region R).card - cost * R.card
  obtain ⟨R, _, hR⟩ := exists_max_image univ score univ_nonempty
  let U := region R
  have hb : 0 ≤ score R := by simpa [score, region] using hR ∅ (mem_univ _)
  dsimp [score] at hb
  have hU := card_le_univ U
  simp [Pair,V] at hU
  rify at hU
  have hbudget := mul_le_mul_of_nonneg_left hU hd.le
  have hcost : 0 ≤ cost := by positivity
  refine ⟨(U, E ∩ U), mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · apply region_mem
    apply Nat.cast_le.mp (le_trans ?_ (Nat.le_ceil _))
    apply (le_div_iff₀ hη).mpr
    apply le_of_mul_le_mul_right (a := (n : ℝ)^2) _ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) (E ∩ U).card]
  · simp only [sparse, mem_filter, mem_univ, true_and]
    linarith [show 0 ≤ cost * R.card by positivity]
  · intro x y h
    simp [decode, compl_adj, E, arcs, h, h.symm, h.ne]
  · intro r
    let B := box r
    have gain := hR (insert r R) (mem_univ _)
    have hi := card_insert_le r R
    have hadd : region (insert r R) = B ∪ U := by simp [region, B, U]
    dsimp only [score] at gain
    rw [hadd, inter_union_distrib_left, ← card_sdiff_add_card, Nat.cast_add] at gain
    have hE := card_union_le (E ∩ B) (E ∩ U)
    rify at hE hi
    -- Each allowed pair is either newly covered or a genuine edge.
    have hsub : arcs (decode U (E ∩ U)) ∩ B ⊆ (B \ U) ∪ (E ∩ B) := by
      intro z
      simp [arcs, decode, compl_adj]
      tauto
    have hcnt := (card_le_card hsub).trans (card_union_le ..)
    rify at hcnt
    nlinarith only [gain, hE, mul_le_mul_of_nonneg_left hi hcost, hcost,
      mul_le_mul_of_nonneg_left hcnt hd.le,
      mul_le_mul_of_nonneg_right hd' (Nat.cast_nonneg (α := ℝ) (E ∩ B).card)]

variable (H : SimpleGraph (V k)) (G T : SimpleGraph (V n))

abbrev Hosts (k n : ℕ) := Sym2 (V k) → SimpleGraph (V n)

-- Nonedges consult the complete graph, so every valid assignment is injective.
def test (s : Finset (Sym2 (V k))) : Hosts k n := fun e =>
  if e ∈ H.edgeFinset then (if e ∈ s then G else T) else ⊤

def valid (P : Hosts k n) (f : V k → V n) := ∀ i j, i ≠ j → (P s(i,j)).Adj (f i) (f j)

def mixed (P : Hosts k n) := Fintype.card {f // valid P f}

lemma mixed_endpoint (J : SimpleGraph (V n)) :
    mixed (fun e => if e ∈ H.edgeFinset then J else ⊤) = J.labelledCopyCount H := by
  simp only [mixed, labelledCopyCount, Fintype.card_eq_nat_card]
  apply Nat.card_congr
  exact {
    toFun := fun f => by
      refine ⟨⟨f.val, fun {i j} h => ?_⟩, ?_⟩
      · simpa [h] using f.prop i j h.ne
      · exact fun i j => not_imp_not.mp fun h => (f.prop i j h).ne
    invFun := fun c => ⟨fun i => c i, fun i j h => by
      by_cases hh : H.Adj i j
      · simpa [hh] using c.toHom.map_rel' hh
      · simpa [hh] using c.injective.ne h⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

abbrev Rest (a b : V k) := {i : V k // i ≠ a ∧ i ≠ b}

def fill {a b : V k} (g : Rest a b → V n) (z : Pair n) (i : V k) : V n :=
  if hi : i = a then z.1 else if hj : i = b then z.2 else g ⟨i,hi,hj⟩

def splitPair (a b : V k) (hab : a ≠ b) :
    (V k → V n) ≃ (Rest a b → V n) × Pair n where
  toFun f := (fun i => f i.1, f a, f b)
  invFun z := fill z.1 z.2
  left_inv f := by funext i; simp [fill]; split_ifs <;> simp_all
  right_inv := by
    rintro ⟨g,x,y⟩
    ext i <;> first | simp [fill, i.property.1, i.property.2] | simp [fill, hab.symm]

lemma count_from_cut {d η : ℝ} (hd : 0 < d) (hd' : d ≤ 1/2) (hη : 0 ≤ η) (hc : CutLE d η T G)
    (s : Finset (Sym2 (V k))) (hs : s ⊆ H.edgeFinset) :
    d^s.card * (mixed (test H G T ∅) : ℝ) ≤ (mixed (test H G T s) : ℝ) + 2 * η * (n : ℝ)^k := by
  -- Since d ≤ 1/2, twice the one-edge error absorbs every preceding error.
  induction s using Finset.induction_on with
  | empty => simp; positivity
  | @insert p s hp ih =>
    rw [insert_subset_iff] at hs
    have hj : d * (mixed (test H G T s) : ℝ) ≤ mixed (test H G T (insert p s)) + η * (n:ℝ)^k := by
      obtain ⟨a,b⟩ := p
      have hab := (show H.Adj a b by simpa using hs.1).ne
      let Q := test H G T s
      -- After fixing the other images, tests avoiding one endpoint depend only on the other.
      let side (c : V k) (g : Rest a b → V n) := univ.filter fun x =>
        ∀ i j, i ≠ j → i ≠ c → j ≠ c → (Q s(i,j)).Adj (fill g (x,x) i) (fill g (x,x) j)
      let sliceRect (g : Rest a b → V n) : Rect n := (side b g, side a g)
      have slice (P : Hosts k n) (ho : ∀ e ≠ s(a,b), P e = Q e) :
          mixed P = ∑ g : Rest a b → V n, (arcs (P s(a,b)) ∩ box (sliceRect g)).card := by
        rw [mixed, Fintype.card_subtype, card_filter, ← (splitPair (n := n) a b hab).symm.sum_comp, Fintype.sum_prod_type]
        apply sum_congr rfl
        intro g _
        change (∑ z : Pair n, if valid P (fill g z) then 1 else 0) = _
        rw [← card_filter]
        congr 1
        ext z
        simp [valid, arcs, box, sliceRect, side]
        grind [fill, Sym2.eq_iff, Adj.symm]
      rw [slice Q (by simp), slice (test H G T (insert s(a,b) s)) (by intro e h; simp [Q,test,h])]
      simp [Q, test, hs.1, hp]
      rw [Finset.mul_sum]
      have hc' := Finset.sum_le_sum (s := (univ : Finset (Rest a b → V n)))
        (fun g _ => hc (sliceRect g))
      have hsize := congrArg (Nat.cast : ℕ → ℝ) (Fintype.card_congr (splitPair (n := n) a b hab))
      simp [sum_add_distrib, Pair, V] at hc' hsize
      rw [hsize]
      linarith only [hc']
    rw [card_insert_of_notMem hp, pow_succ]
    have h₁ := mul_le_mul_of_nonneg_left (ih hs.2) hd.le
    have h₂ := mul_le_mul_of_nonneg_right hd' (show 0 ≤ 2 * η * (n : ℝ)^k by positivity)
    nlinarith only [h₁, h₂, hj]

lemma code_budget {δ : ℝ} (hδ : 0 < δ) : ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ M,
    ∀ᶠ n : ℕ in atTop, ((codes n M d).card : ℝ) ≤ (2:ℝ)^(δ * n^2) := by
  let w := (2:ℝ)^(δ/2)
  have hw : 1 < w := Real.one_lt_rpow (by norm_num) (by positivity)
  obtain ⟨t, ht, hsmall⟩ := exists_between (lt_min zero_lt_one (sub_pos.mpr hw))
  obtain ⟨ht', htw⟩ := lt_min_iff.mp hsmall
  have hcont : Continuous (fun x : ℝ => w * t^x) := by fun_prop (disch := positivity)
  have hev := hcont.continuousAt.tendsto.eventually_const_lt
    (show t+1 < w * t^(0:ℝ) by simp; linarith)
  obtain ⟨d, hdw, hd, hd'⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num))).exists
  refine ⟨d, hd, hd'.le, fun M => ?_⟩
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hw).eventually_ge_atTop (4^M)] with n hn
  -- Weight a payload by t to the power of its size and sum over all subsets.
  have hs : ((sparse n d).card : ℝ) ≤ w^(n^2) := by
    apply le_of_mul_le_mul_right (a := t^(d*(n:ℝ)^2)) _ (Real.rpow_pos_of_pos ht _)
    calc
      _ ≤ ∑ S ∈ sparse n d, t^S.card := by
        rw [← nsmul_eq_mul]
        apply card_nsmul_le_sum
        intro S hS
        rw [← Real.rpow_natCast t S.card]
        exact Real.rpow_le_rpow_of_exponent_ge ht ht'.le (mem_filter.mp hS).2
      _ ≤ ∑ S : Finset (Pair n), t^S.card := sum_le_univ_sum_of_nonneg (by intros; positivity)
      _ = (t+1)^(n^2) := by simpa [Pair, V, pow_two] using Fintype.sum_pow_mul_eq_add_pow (Pair n) t 1
      _ ≤ _ := by
        rw [show (n:ℝ)^2 = ((n^2:ℕ):ℝ) by norm_cast, Real.rpow_mul_natCast ht.le, ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hdw.le _
  have hm : (menus n M).card ≤ (4^M)^n := by
    apply card_image_le.trans
    simp [Rect, V, ← mul_pow, ← pow_mul, Nat.mul_comm]
  rw [codes, card_product, Nat.cast_mul,
    show δ*(n:ℝ)^2 = (δ/2+δ/2) * ((n^2:ℕ):ℝ) by push_cast; ring,
    Real.rpow_mul_natCast (by norm_num), Real.rpow_add (by norm_num), mul_pow]
  apply mul_le_mul _ hs (by positivity) (by positivity)
  apply (Nat.cast_le.mpr hm).trans
  push_cast
  simpa [← pow_mul,pow_two] using pow_le_pow_left₀ (by positivity) hn n

end OMA.E59

end

open OMA.E59 in
theorem OMA.solution : OMA.R_Erdos59_erdos_59_variants_erdos_frankl_rodl_R1.H1 := by
  intro k H _ δ hδ γ hγ
  obtain ⟨d, hd, hd', hcode⟩ := code_budget hδ
  let m := H.edgeFinset.card
  let η : ℝ := γ * (d/2)^m / 2
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [eventually_ge_atTop 1, hcode ⌈d/η⌉₊] with n hn hcode
  let C := ((codes n ⌈d/η⌉₊ d).image fun p => decode p.1 p.2).filter fun T =>
    (T.copyCount H : ℝ) ≤ γ * n^k
  refine ⟨C, ?_, fun _ h => (mem_filter.mp h).2, ?_⟩
  · exact (Nat.cast_le.mpr ((card_filter_le ..).trans card_image_le)).trans hcode
  · intro G hG
    obtain ⟨p, hp, hle, hc⟩ := exists_code hn G hd hd' hη
    let T := decode p.1 p.2
    have hh := count_from_cut H G T (half_pos hd) (by linarith) hη.le hc _ Subset.rfl
    unfold test at hh
    simp +contextual only [notMem_empty, if_false, if_true, mixed_endpoint,
      labelledCopyCount_eq_zero.mpr hG, Nat.cast_zero, zero_add] at hh
    refine ⟨T, mem_filter.mpr ⟨mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩, hle⟩
    apply le_trans (Nat.cast_le.mpr copyCount_le_labelledCopyCount)
    apply le_of_mul_le_mul_left (a := (d/2)^m) _ (by positivity)
    dsimp [η, m] at hh ⊢
    linarith only [hh]
