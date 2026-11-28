import OMAStatements.S_mse_4815847
import Mathlib

/-!
# Integer directions for cutting Pascal's triangle

A finite grid of side N has critical slopes p/q with |p| ≤ N and 1 ≤ q ≤ N.
After normalizing the larger of the two normal coordinates, a mediant between
the nearest critical slopes strictly below and above the original direction
preserves every strict comparison. Ties in the old direction can break safely
because the original line avoids the vertices. An integer threshold just above
the last negative vertex then preserves both regions.

The resulting finite test for each N uses only integers and binomial coefficients.
The two ranges separate the finite cases checked independently by an exact
slope sweep from the unbounded remainder. Source: Math Stack Exchange 4815847.
-/

namespace OMA.R_mse_4815847_R1

open OMA.S_mse_4815847

/-- An order-preserving rational direction with bounded numerator and denominator. -/
private lemma choose_slope (N : ℤ) (hN : 2 ≤ N) (t : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) :
    ∃ u v : ℤ, -2*N ≤ u ∧ u ≤ 2*N ∧ 0 < v ∧ v ≤ 2*N ∧
      ∀ i j : ℤ, -N ≤ i → i ≤ N → -N ≤ j → j ≤ N →
        t * (i : ℝ) + (j : ℝ) < 0 → u*i + v*j < 0 := by
  classical
  let K := Finset.Icc (-N) N ×ˢ Finset.Icc (1:ℤ) N
  let val (p : ℤ × ℤ) := (p.1 : ℝ) / p.2
  let L := K.filter (fun p => val p < t)
  let U := K.filter (fun p => t < val p)
  have hL : (-2,1) ∈ L := by
    simp only [L, K, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨by omega,by omega⟩,by norm_num,by omega⟩,?_⟩
    norm_num [val]
    linarith [ht.1]
  have hU : (2,1) ∈ U := by
    simp only [U, K, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨by omega,by omega⟩,by norm_num,by omega⟩,?_⟩
    norm_num [val]
    linarith [ht.2]
  obtain ⟨lo, hlo, hmax⟩ := L.exists_max_image val ⟨_, hL⟩
  obtain ⟨hi, hhi, hmin⟩ := U.exists_min_image val ⟨_, hU⟩
  obtain ⟨⟨⟨hl₁,hl₂⟩,hl₃,hl₄⟩,hlt⟩ :
      ((-N ≤ lo.1 ∧ lo.1 ≤ N) ∧ 1 ≤ lo.2 ∧ lo.2 ≤ N) ∧ val lo < t := by
    simpa [L, K] using hlo
  obtain ⟨⟨⟨hh₁,hh₂⟩,hh₃,hh₄⟩,htl⟩ :
      ((-N ≤ hi.1 ∧ hi.1 ≤ N) ∧ 1 ≤ hi.2 ∧ hi.2 ≤ N) ∧ t < val hi := by
    simpa [U, K] using hhi
  have hlp : 0 < (lo.2 : ℝ) := by exact_mod_cast (show 0 < lo.2 by omega)
  have hhp : 0 < (hi.2 : ℝ) := by exact_mod_cast (show 0 < hi.2 by omega)
  let u := lo.1 + hi.1
  let v := lo.2 + hi.2
  have hv : 0 < v := by dsimp [v]; omega
  have hvr : 0 < (v : ℝ) := by exact_mod_cast hv
  have hcross := (div_lt_div_iff₀ hlp hhp).mp (show val lo < val hi from hlt.trans htl)
  have hlow : val lo < (u : ℝ)/v := by
    apply (div_lt_div_iff₀ hlp hvr).2
    dsimp [u,v]; push_cast; nlinarith
  have hhigh : (u : ℝ)/v < val hi := by
    apply (div_lt_div_iff₀ hvr hhp).2
    dsimp [u,v]; push_cast; nlinarith
  refine ⟨u,v,by dsimp [u]; omega,by dsimp [u]; omega,hv,by dsimp [v]; omega,?_⟩
  intro i j hi₁ hi₂ hj₁ hj₂ hsign
  rcases lt_trichotomy i 0 with hneg | rfl | hpos
  · have hip : 0 < ((-i : ℤ) : ℝ) := by exact_mod_cast (show 0 < -i by omega)
    have htj : val (j,-i) < t := by
      apply (div_lt_iff₀ hip).2
      push_cast
      linarith
    have hmem : (j,-i) ∈ L := by
      simp only [L, K, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨hj₁,hj₂⟩,by omega,by omega⟩,htj⟩
    have h := (div_lt_div_iff₀ hip hvr).mp ((hmax _ hmem).trans_lt hlow)
    change (j:ℝ)*(v:ℝ) < (u:ℝ)*((-i:ℤ):ℝ) at h
    exact_mod_cast (show (u:ℝ)*i+(v:ℝ)*j < 0 by push_cast at h; nlinarith)
  · simp at hsign ⊢
    exact mul_neg_of_pos_of_neg hv (by exact_mod_cast hsign)
  · have hip : 0 < (i : ℝ) := by exact_mod_cast hpos
    have htj : t < val (-j,i) := by
      apply (lt_div_iff₀ hip).2
      push_cast
      linarith
    have hmem : (-j,i) ∈ U := by
      simp only [U, K, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨by omega,by omega⟩,by omega,hi₂⟩,htj⟩
    have h := (div_lt_div_iff₀ hvr hip).mp (hhigh.trans_le (hmin _ hmem))
    change (u:ℝ)*(i:ℝ) < ((-j:ℤ):ℝ)*(v:ℝ) at h
    exact_mod_cast (show (u:ℝ)*i+(v:ℝ)*j < 0 by push_cast at h; nlinarith)

private lemma dominant_normal {N : ℤ} (hN : 2 ≤ N) {a b : ℝ}
    (hb : 0 < b) (hab : |a| ≤ b) :
    ∃ u v : ℤ, |u| ≤ 2*N ∧ |v| ≤ 2*N ∧
      ∀ i j : ℤ, |i| ≤ N → |j| ≤ N → a*i+b*j < 0 → u*i+v*j < 0 := by
  obtain ⟨al,au⟩ := abs_le.mp hab
  have ht : -1 ≤ a/b ∧ a/b ≤ 1 :=
    ⟨(le_div_iff₀ hb).2 (by linarith), (div_le_iff₀ hb).2 (by linarith)⟩
  obtain ⟨u,v,ul,uu,vp,vu,H⟩ := choose_slope N hN _ ht
  refine ⟨u,v,abs_le.mpr ⟨by linarith,uu⟩,by simpa [abs_of_pos vp] using vu,?_⟩
  intro i j hi hj h
  apply H i j (abs_le.mp hi).1 (abs_le.mp hi).2 (abs_le.mp hj).1 (abs_le.mp hj).2
  have e : a/b*i+j = (a*i+b*j)/b := by field_simp
  rw [e]
  exact div_neg_of_neg_of_pos h hb

private lemma second_normal {N : ℤ} (hN : 2 ≤ N) (a b : ℝ) (hab : |a| ≤ |b|) :
    ∃ u v : ℤ, |u| ≤ 2*N ∧ |v| ≤ 2*N ∧
      ∀ i j : ℤ, |i| ≤ N → |j| ≤ N → a*i+b*j < 0 → u*i+v*j < 0 := by
  rcases lt_trichotomy b 0 with hn | rfl | hp
  · obtain ⟨u,v,hu,hv,H⟩ := dominant_normal hN (neg_pos.mpr hn)
      (show |a| ≤ -b by simpa [abs_of_neg hn] using hab)
    refine ⟨u,-v,hu,by simpa using hv,?_⟩
    intro i j hi hj h
    have hh := H i (-j) hi (by simpa using hj) (by simpa using h)
    linarith
  · have ha : a = 0 := by simpa using hab
    refine ⟨0,0,by simp; omega,by simp; omega,?_⟩
    simp [ha]
  · exact dominant_normal hN hp (by simpa [abs_of_pos hp] using hab)

private lemma integer_normal {N : ℤ} (hN : 2 ≤ N) (a b : ℝ) :
    ∃ u v : ℤ, |u| ≤ 2*N ∧ |v| ≤ 2*N ∧
      ∀ i j : ℤ, |i| ≤ N → |j| ≤ N → a*i+b*j < 0 → u*i+v*j < 0 := by
  rcases le_total |a| |b| with h | h
  · exact second_normal hN a b h
  · obtain ⟨u,v,hu,hv,H⟩ := second_normal hN b a h
    refine ⟨v,u,hv,hu,?_⟩
    intro i j hi hj h
    simpa only [add_comm] using H j i hj hi (by simpa only [add_comm] using h)

/-- Preserve the two strict half-planes on a bounded grid by an integer threshold. -/
private lemma integer_cut {N : ℕ} (hN : 2 ≤ N) (S : Finset (ℕ × ℕ))
    (hbox : ∀ p ∈ S, p.1 ≤ N ∧ p.2 ≤ N) (a b c : ℝ)
    (havoid : ∀ p ∈ S, a*p.1+b*p.2+c ≠ 0) :
    ∃ u v d : ℤ, |u| ≤ 2*(N:ℤ) ∧ |v| ≤ 2*(N:ℤ) ∧ |d| ≤ 4*(N:ℤ)^2+1 ∧
      ∀ p ∈ S, (a*p.1+b*p.2+c < 0 ↔ u*p.1+v*p.2 ≤ d) ∧
        (0 < a*p.1+b*p.2+c ↔ d < u*p.1+v*p.2) := by
  classical
  obtain ⟨u,v,hu,hv,H⟩ := integer_normal (show 2 ≤ (N:ℤ) by exact_mod_cast hN) a b
  let g (p : ℕ × ℕ) : ℤ := u*p.1+v*p.2
  let B : ℤ := 4*(N:ℤ)^2
  have hbnd (p) (hp : p ∈ S) : |g p| ≤ B := by
    obtain ⟨hx,hy⟩ := hbox p hp
    calc
      |g p| ≤ |u| * (p.1:ℤ)+|v| * (p.2:ℤ) := by
        simpa [g, abs_mul] using abs_add_le (u*(p.1:ℤ)) (v*(p.2:ℤ))
      _ ≤ (2*(N:ℤ))*N+(2*(N:ℤ))*N := by
        gcongr
      _ = B := by dsimp [B]; ring
  let neg := S.filter (fun p => a*p.1+b*p.2+c < 0)
  let Z := insert (-B-1) (neg.image g)
  obtain ⟨d,hd,hmax⟩ := Z.exists_max_image id (Finset.insert_nonempty _ _)
  have hsep (p q) (hp : p ∈ S) (hq : q ∈ S)
      (hneg : a*p.1+b*p.2+c < 0) (hpos : 0 < a*q.1+b*q.2+c) : g p < g q := by
    obtain ⟨px,py⟩ := hbox p hp
    obtain ⟨qx,qy⟩ := hbox q hq
    have HH := H ((p.1:ℤ)-q.1) ((p.2:ℤ)-q.2)
      (abs_le.mpr ⟨by omega,by omega⟩) (abs_le.mpr ⟨by omega,by omega⟩)
      (by push_cast; linarith)
    dsimp [g]; linarith
  have hd' : d = -B-1 ∨ ∃ p ∈ neg, g p = d := by simpa [Z] using hd
  have hdlo : -B-1 ≤ d := hmax _ (by simp [Z])
  have hdhi : d ≤ B+1 := by
    rcases hd' with rfl | ⟨p,hp,rfl⟩
    · dsimp [B]; nlinarith [sq_nonneg (N:ℤ)]
    · have := (abs_le.mp (hbnd p (Finset.mem_filter.mp hp).1)).2
      omega
  refine ⟨u,v,d,hu,hv,abs_le.mpr ⟨by dsimp [B] at hdlo; linarith,hdhi⟩,?_⟩
  intro p hp
  rcases lt_or_gt_of_ne (havoid p hp) with h | h
  · have hle : g p ≤ d := hmax _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g
        (Finset.mem_filter.mpr ⟨hp,h⟩)))
    exact ⟨iff_of_true h hle, iff_of_false (not_lt.mpr h.le) (not_lt.mpr hle)⟩
  · have hlt : d < g p := by
      rcases hd' with rfl | ⟨q,hq,rfl⟩
      · have := (abs_le.mp (hbnd p hp)).1
        omega
      · have hq' := Finset.mem_filter.mp hq
        exact hsep q p hq'.1 hp hq'.2 h
    exact ⟨iff_of_false (not_lt.mpr h.le) (not_le.mpr hlt), iff_of_true h hlt⟩

def H1 : Prop := ∀ N : ℕ, 2 ≤ N → N ≤ 250 → ∀ u v d : ℤ, |u| ≤ 2*(N:ℤ) → |v| ≤ 2*(N:ℤ) → |d| ≤ 4*(N:ℤ)^2+1 →
    (∑ p ∈ (entries N).filter (fun p => d < u * (p.1:ℤ) + v*p.2), Nat.choose p.1 p.2) ≠
      ∑ p ∈ (entries N).filter (fun p => u * (p.1:ℤ) + v*p.2 ≤ d), Nat.choose p.1 p.2

def H2 : Prop := ∀ N : ℕ, 250 < N → ∀ u v d : ℤ, |u| ≤ 2*(N:ℤ) → |v| ≤ 2*(N:ℤ) → |d| ≤ 4*(N:ℤ)^2+1 →
    (∑ p ∈ (entries N).filter (fun p => d < u * (p.1:ℤ) + v*p.2), Nat.choose p.1 p.2) ≠
      ∑ p ∈ (entries N).filter (fun p => u * (p.1:ℤ) + v*p.2 ≤ d), Nat.choose p.1 p.2


theorem main : H1 → H2 → type_of% @OMA.S_mse_4815847.main := by
  classical
  intro small large N hN a b c avoid
  have hbox (p) (hp : p ∈ entries N) : p.1 ≤ N ∧ p.2 ≤ N := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have := Finset.mem_range.mp ha
    have := Finset.mem_range.mp hb
    omega
  obtain ⟨u,v,d,hu,hv,hd,hclass⟩ := integer_cut hN (entries N) hbox a b c avoid
  have eq₁ : (entries N).filter (fun p => 0 < side a b c p) =
      (entries N).filter (fun p => d < u*(p.1:ℤ)+v*p.2) :=
    Finset.filter_congr fun p hp => (hclass p hp).2
  have eq₂ : (entries N).filter (fun p => side a b c p < 0) =
      (entries N).filter (fun p => u*(p.1:ℤ)+v*p.2 ≤ d) :=
    Finset.filter_congr fun p hp => (hclass p hp).1
  rw [eq₁,eq₂]
  by_cases hn : N ≤ 250
  · exact small N hN hn u v d hu hv hd
  · exact large N (by omega) u v d hu hv hd

end OMA.R_mse_4815847_R1
