import OMAReductions.R_Erdos626_erdos_626_variants_h_even_conjecture_R1_H2_R1
import Mathlib

/-! A reduction of the remaining even-girth lower bound.
For m=6 it suffices to bound the independence number of graphs of girth at least seven
at dyadic orders. For even m ≥ 8 it suffices to construct chromatic witnesses with
at most 2^k vertices at scale k. Adding isolated vertices preserves the girth bound,
and an arbitrarily small loss in the exponent absorbs the gap between consecutive scales.
No construction satisfying either open hypothesis is assumed in the supporting lemmas. -/

namespace OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1_H2_R1_H2_R1

open Filter

open SimpleGraph Erdos626

lemma egirth_le_map_of_embedding {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) :
    G.egirth ≤ (G.map f).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro a p hp
  let i := SimpleGraph.Embedding.map f G
  let S := Set.range i
  have hs (x : W) (hx : x ∈ p.support) : x ∈ S := by
    obtain ⟨e, he, hx⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
      (fun hn => hp.ne_nil (SimpleGraph.Walk.eq_nil_iff_nil.mpr hn))).mp hx
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hx
    obtain ⟨z, w, _, hz, _⟩ := (SimpleGraph.map_adj f G x y).mp (p.adj_of_mem_edges he)
    exact ⟨z, hz⟩
  let q := p.induce S hs
  have hmap : q.map (SimpleGraph.Embedding.induce S).toHom = p :=
    SimpleGraph.Walk.map_induce _ _
  have hq : q.IsCycle := SimpleGraph.Walk.IsCycle.of_map (hmap.symm ▸ hp)
  have hlen : q.length = p.length :=
    (q.length_map (SimpleGraph.Embedding.induce S).toHom).symm.trans
      (congrArg SimpleGraph.Walk.length hmap)
  calc
    G.egirth = ((G.map f).induce S).egirth := i.isoInduceRange.egirth_eq
    _ ≤ q.length := SimpleGraph.egirth_le_length hq
    _ = _ := by rw [hlen]

lemma h_set_bdd (m n : ℕ) :
    BddAbove {c : ℕ | ∃ G : SimpleGraph (Fin n), (m : ℕ∞) < G.egirth ∧ G.chromaticNumber = c} := by
  refine ⟨n, ?_⟩
  rintro c ⟨G, _, hc⟩
  have hle := G.chromaticNumber_le_card
  rw [hc, Fintype.card_fin] at hle
  exact_mod_cast hle

lemma h_monotone_vertices (m : ℕ) : Monotone (h m) := by
  intro n N hN
  apply csSup_le'
  rintro c ⟨G, hg, hc⟩
  let f := Fin.castLEEmb hN
  let K := G.map f
  have hk : K.chromaticNumber ≠ ⊤ := lt_top_iff_ne_top.mp
    (lt_of_le_of_lt K.chromaticNumber_le_card (by simp))
  have hkcast := ENat.natCast_toNat_eq_self.mpr hk
  have hle := SimpleGraph.chromaticNumber_mono_of_hom (SimpleGraph.Embedding.map f G).toHom
  change G.chromaticNumber ≤ K.chromaticNumber at hle
  rw [hc, ← hkcast] at hle
  apply le_trans (ENat.natCast_le_natCast.mp hle)
  exact le_csSup (h_set_bdd m N) ⟨K, lt_of_lt_of_le hg (egirth_le_map_of_embedding G f), hkcast.symm⟩



lemma card_le_alpha_mul_chromatic {n : ℕ} (G : SimpleGraph (Fin n)) :
    n ≤ G.indepNum * G.chromaticNumber.toNat := by
  classical
  obtain ⟨C⟩ := G.colorable_chromaticNumber_of_fintype
  have fibers (c : Fin G.chromaticNumber.toNat) :
      (Finset.univ.filter (fun v : Fin n => C v = c)).card ≤ G.indepNum := by
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    simpa [SimpleGraph.Coloring.colorClass, Set.ext_iff] using C.isIndepSet_colorClass c
  have h := Finset.card_le_mul_card_image_of_maps_to
    (f := fun v : Fin n => C v) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) G.indepNum (fun c _ => fibers c)
  simpa using h

lemma chromatic_lower_of_small_indep {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    {a : ℝ} (ha : (G.indepNum : ℝ) ≤ (n : ℝ) ^ (1 - a)) :
    (n : ℝ)^a ≤ (G.chromaticNumber.toNat : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ) ^ (1 - a) := Real.rpow_pos_of_pos hn' _
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    (n : ℝ) ^ (1-a) * n ^ a = n := by
      rw [← Real.rpow_add hn', sub_add_cancel, Real.rpow_one]
    _ ≤ (G.indepNum : ℝ) * (G.chromaticNumber.toNat : ℝ) := by
      exact_mod_cast card_le_alpha_mul_chromatic G
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (by positivity)




lemma dyadic_lower {f : ℕ → ℕ} (hf : Monotone f) {r : ℝ} (hr : 0 < r)
    (hgrid : ∀ d > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ((2 : ℝ) ^ k) ^ (r - d) ≤ (f (2 ^ k) : ℝ))
    (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (r - e) ≤ (f n : ℝ) := by
  let d := min (e / 2) (r / 2)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hde : 2*d ≤ e := by dsimp [d]; linarith [min_le_left (e/2) (r/2)]
  have hdr : 2*d ≤ r := by dsimp [d]; linarith [min_le_right (e/2) (r/2)]
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hgrid d hd)
  obtain ⟨J, hJ⟩ := exists_nat_ge (r/d)
  refine eventually_atTop.2 ⟨2 ^ max K J, ?_⟩
  intro n hn
  let k := Nat.log 2 n
  have hmax : max K J ≤ k := Nat.le_log_of_pow_le (by decide) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from hnpos)
  have hlarge : r ≤ (k : ℝ)*d := by
    apply (div_le_iff₀ hd).1
    exact hJ.trans (by exact_mod_cast (le_max_right K J).trans hmax)
  have hnupper : (n : ℝ) ≤ (2 : ℝ) ^ (k+1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (b := 2) (by decide) n).le
  have hkle : (2 : ℕ)^k ≤ n := Nat.pow_log_le_self 2 hnpos.ne'
  calc
    (n : ℝ) ^ (r-e) ≤ (n : ℝ) ^ (r-2*d) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ ≤ ((2 : ℝ)^(k+1)) ^ (r-2*d) :=
      Real.rpow_le_rpow (by positivity) hnupper (by linarith)
    _ = (2 : ℝ) ^ (((k : ℝ)+1)*(r-2*d)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast
      rfl
    _ ≤ (2 : ℝ) ^ ((k : ℝ)*(r-d)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith only [hlarge, hd]
    _ = ((2 : ℝ)^k) ^ (r-d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (f (2^k) : ℝ) := hK k ((le_max_left K J).trans hmax)
    _ ≤ (f n : ℝ) := by exact_mod_cast hf hkle

/-- A Ramsey construction for girth at least seven. The bound asks for small
independent sets at dyadic orders only. -/
def H1 : Prop :=
  ∀ d > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
    ∃ G : SimpleGraph (Fin (2 ^ k)), (6 : ℕ∞) < G.egirth ∧
      (G.indepNum : ℝ) ≤ ((2 : ℝ) ^ k) ^ (3 / 4 + d)

/-- The corresponding constructions for forbidden cycle lengths up to even m ≥ 8. -/
def H2 : Prop :=
  ∀ m : ℕ, Even m → 8 ≤ m → ∀ d > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
    ∃ v ≤ 2 ^ k, ∃ G : SimpleGraph (Fin v), ∃ c : ℕ,
      (m : ℕ∞) < G.egirth ∧ G.chromaticNumber = c ∧
      ((2 : ℝ) ^ k) ^ (2 / ((m : ℝ) + 2) - d) ≤ (c : ℝ)

lemma from_witnesses (m : ℕ) (r : ℝ) (hr : 0 < r)
    (hw : ∀ d > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ∃ v ≤ 2 ^ k, ∃ G : SimpleGraph (Fin v), ∃ c : ℕ,
        (m : ℕ∞) < G.egirth ∧ G.chromaticNumber = c ∧
        ((2 : ℝ) ^ k) ^ (r - d) ≤ (c : ℝ))
    (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (r - e) ≤ (Erdos626.h m n : ℝ) := by
  apply dyadic_lower (h_monotone_vertices m) hr _ e he
  intro d hd
  filter_upwards [hw d hd] with k h
  obtain ⟨v, hv, G, c, hg, hc, hl⟩ := h
  have hb : c ≤ Erdos626.h m v := le_csSup (h_set_bdd m v) ⟨G, hg, hc⟩
  exact hl.trans (by exact_mod_cast hb.trans (h_monotone_vertices m hv))

theorem main : H1 → H2 → OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1_H2_R1.H2 := by
  intro h₁ h₂ m hm hm6 e he
  by_cases h6 : m = 6
  · subst m
    apply from_witnesses 6 _ (by positivity) _ e he
    intro d hd
    filter_upwards [h₁ d hd] with k hk
    obtain ⟨G, hg, hα⟩ := hk
    have hn : 0 < (2 : ℕ) ^ k := by positivity
    have hfin : G.chromaticNumber ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card
    refine ⟨2 ^ k, le_rfl, G, G.chromaticNumber.toNat, hg,
      (ENat.natCast_toNat_eq_self.mpr hfin).symm, ?_⟩
    push_cast at *
    convert chromatic_lower_of_small_indep hn G (a := (1 / 4 - d)) (by
      push_cast
      convert hα using 2 <;> ring) using 1 <;> push_cast <;> norm_num
  · have hm8 : 8 ≤ m := by obtain ⟨j, hj⟩ := hm; omega
    exact from_witnesses m _ (by positivity) (h₂ m hm hm8) e he

end OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1_H2_R1_H2_R1
