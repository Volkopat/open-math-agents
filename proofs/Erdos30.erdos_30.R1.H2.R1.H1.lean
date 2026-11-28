import OMAReductions.R_Erdos30_erdos_30_R1_H2_R1

/-!
# The cut inequality for perfect difference sets (step H1 of Erdos30.erdos_30.R1.H2.R1)

Let `D` be a perfect difference set in `ZMod m`, `x ∉ D`, and `A` an integer Sidon set with
`x.val ∈ A`. For `d ∈ D` let `(b d, c d)` be the pair of `D` with `b d - c d = x - d`.

* `b` is injective on `D` (hence a permutation of `D`), and `c` takes each value at most twice,
  both because `D` is Sidon and `x ∉ D`.
* As integers `b + d - x - c ∈ {0, m, -m}`. Writing `p` and `g` for the two test functions of
  the statement, a case check gives, for every `d ∈ D`,
  `m ≤ 4 m [b + d = x + c] + 2 (p d + p (b d)) + g (c d)`.
* If `b + d = x + c` holds as integers, one of `d, b d, c d` has its value outside `A`
  (otherwise `A` would not be Sidon, as `x ∉ D`); so at most `4 ℓ` such `d`, where `ℓ` counts the
  marks of `D` outside `A`.

Summing, with `Σ p (b d) = Σ p d` and `Σ g (c d) ≤ 2 Σ g d`, gives the claim.
-/

namespace OMA.P11Erdos30

open Finset

/-- The first test function of the statement. -/
def pf (m : ℕ) (x d : ZMod m) : ℤ :=
  if d.val < x.val then (x.val : ℤ) - 2 * d.val else 2 * (d.val : ℤ) - x.val - m

/-- The second test function of the statement. -/
def gf (m : ℕ) (d : ZMod m) : ℤ :=
  max 0 ((m : ℤ) - 4 * min (d.val : ℤ) ((m : ℤ) - d.val))

lemma gf_nonneg (m : ℕ) (y : ZMod m) : 0 ≤ gf m y := le_max_left _ _

lemma gf_ge1 (m : ℕ) (y : ZMod m) : (m : ℤ) - 4 * (y.val : ℤ) ≤ gf m y := by
  unfold gf
  have h := min_le_left (y.val : ℤ) ((m : ℤ) - y.val)
  exact le_trans (by linarith) (le_max_right _ _)

lemma gf_ge2 (m : ℕ) (y : ZMod m) : 4 * (y.val : ℤ) - 3 * m ≤ gf m y := by
  unfold gf
  have h := min_le_right (y.val : ℤ) ((m : ℤ) - y.val)
  exact le_trans (by linarith) (le_max_right _ _)

/-- Two sums of residues below `m` that agree modulo `m` differ by `0` or by `± m`. -/
lemma sum_cases {m a b c d : ℕ} (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m)
    (h : (a + b) % m = (c + d) % m) :
    a + b = c + d ∨ a + b = c + d + m ∨ a + b + m = c + d := by
  have e1 := Nat.div_add_mod (a + b) m
  have e2 := Nat.div_add_mod (c + d) m
  have hm : 0 < m := by omega
  have q1 : (a + b) / m < 2 := by
    rw [Nat.div_lt_iff_lt_mul hm]
    omega
  have q2 : (c + d) / m < 2 := by
    rw [Nat.div_lt_iff_lt_mul hm]
    omega
  generalize (a + b) / m = u at e1 q1
  generalize (c + d) / m = v at e2 q2
  generalize (a + b) % m = r at e1 h
  generalize (c + d) % m = w at e2 h
  interval_cases u <;> interval_cases v <;> omega

/-- The pointwise inequality, in integers. -/
lemma per_d {m x b d c : ℕ} (hx : x < m) (hb : b < m) (hd : d < m) (hc : c < m)
    (hdx : d ≠ x) (hbx : b ≠ x)
    (rel : b + d = x + c ∨ b + d = x + c + m ∨ b + d + m = x + c) {G : ℤ} (hg0 : 0 ≤ G)
    (hg1 : (m : ℤ) - 4 * (c : ℤ) ≤ G) (hg2 : 4 * (c : ℤ) - 3 * m ≤ G) :
    (m : ℤ) ≤ 4 * m * (if b + d = x + c then (1 : ℤ) else 0) +
      2 * ((if d < x then (x : ℤ) - 2 * d else 2 * (d : ℤ) - x - m) +
        (if b < x then (x : ℤ) - 2 * b else 2 * (b : ℤ) - x - m)) + G := by
  rcases rel with r | r | r <;> split_ifs <;> omega

theorem main_bound (m : ℕ) [NeZero m] (D : Finset (ZMod m)) (A : Finset ℕ) (x : ZMod m)
    (hD : IsSidon (D : Set (ZMod m))) (hfull : ∀ z : ZMod m, z ≠ 0 → ∃ b ∈ D, ∃ c ∈ D, b - c = z)
    (hA : IsSidon (A : Set ℕ)) (hx : x ∉ D) (hxA : x.val ∈ A) :
    (m : ℤ) * D.card ≤ 16 * m * ((D.filter (fun d => d.val ∉ A)).card : ℤ) +
      4 * (∑ d ∈ D, pf m x d) + 2 * (∑ d ∈ D, gf m d) := by
  classical
  -- the representation of `x - d`
  have hex : ∀ d ∈ D, ∃ q : ZMod m × ZMod m, q.1 ∈ D ∧ q.2 ∈ D ∧ q.1 - q.2 = x - d := by
    intro d hd
    have hz : x - d ≠ 0 := by
      intro h
      apply hx
      rw [sub_eq_zero.mp h]
      exact hd
    obtain ⟨b, hb, c, hc, h⟩ := hfull (x - d) hz
    exact ⟨(b, c), hb, hc, h⟩
  choose! f hf using hex
  have hbD : ∀ d ∈ D, (f d).1 ∈ D := fun d hd => (hf d hd).1
  have hcD : ∀ d ∈ D, (f d).2 ∈ D := fun d hd => (hf d hd).2.1
  have hsum : ∀ d ∈ D, (f d).1 + d = x + (f d).2 := by
    intro d hd
    have h := (hf d hd).2.2
    linear_combination h
  have hDs : ∀ i₁ ∈ D, ∀ j₁ ∈ D, ∀ i₂ ∈ D, ∀ j₂ ∈ D, i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁) := fun i₁ h₁ j₁ h₂ i₂ h₃ j₂ h₄ h =>
    hD i₁ (mem_coe.mpr h₁) j₁ (mem_coe.mpr h₂) i₂ (mem_coe.mpr h₃) j₂ (mem_coe.mpr h₄) h
  -- `b` is injective on `D`
  have hbinj : ∀ d₁ ∈ D, ∀ d₂ ∈ D, (f d₁).1 = (f d₂).1 → d₁ = d₂ := by
    intro d₁ h₁ d₂ h₂ he
    have s1 := hsum d₁ h₁
    have s2 := hsum d₂ h₂
    have key : d₁ + (f d₂).2 = d₂ + (f d₁).2 := by
      linear_combination s1 - s2 - he
    rcases hDs d₁ h₁ d₂ h₂ (f d₂).2 (hcD d₂ h₂) (f d₁).2 (hcD d₁ h₁) key with ⟨e, -⟩ | ⟨e1, -⟩
    · exact e
    · exfalso
      apply hx
      have hbx : (f d₁).1 = x := by linear_combination s1 - e1
      rw [← hbx]
      exact hbD d₁ h₁
  -- `c` takes each value at most twice on `D`
  have hcfib : ∀ y, (D.filter (fun d => (f d).2 = y)).card ≤ 2 := by
    intro y
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨d₁, h₁, d₂, h₂, d₃, h₃, n12, n13, n23⟩ := Finset.two_lt_card.mp hlt
    rw [Finset.mem_filter] at h₁ h₂ h₃
    have pair : ∀ u v : ZMod m, u ∈ D → v ∈ D → (f u).2 = y → (f v).2 = y → u ≠ v →
        u = (f v).1 := by
      intro u v hu hv hcu hcv huv
      have su := hsum u hu
      have sv := hsum v hv
      have key : (f u).1 + u = (f v).1 + v := by
        rw [su, sv, hcu, hcv]
      rcases hDs (f u).1 (hbD u hu) (f v).1 (hbD v hv) u hu v hv key with ⟨-, e⟩ | ⟨-, e⟩
      · exact absurd e huv
      · exact e
    have e2 := pair d₂ d₁ h₂.1 h₁.1 h₂.2 h₁.2 (Ne.symm n12)
    have e3 := pair d₃ d₁ h₃.1 h₁.1 h₃.2 h₁.2 (Ne.symm n13)
    exact n23 (e2.trans e3.symm)
  -- integer form of `b + d = x + c`
  have hint : ∀ d ∈ D, ((f d).1.val + d.val = x.val + (f d).2.val) ∨
      ((f d).1.val + d.val = x.val + (f d).2.val + m) ∨
      ((f d).1.val + d.val + m = x.val + (f d).2.val) := by
    intro d hd
    apply sum_cases (ZMod.val_lt (f d).1) (ZMod.val_lt d) (ZMod.val_lt x) (ZMod.val_lt (f d).2)
    rw [← ZMod.natCast_eq_natCast_iff']
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hsum d hd
  -- the pointwise inequality
  have hper : ∀ d ∈ D, (m : ℤ) ≤
      4 * m * (if (f d).1.val + d.val = x.val + (f d).2.val then (1 : ℤ) else 0) +
        2 * (pf m x d + pf m x (f d).1) + gf m (f d).2 := by
    intro d hd
    have hdx : d.val ≠ x.val := by
      intro h
      apply hx
      rw [← ZMod.val_injective m h]
      exact hd
    have hbx : (f d).1.val ≠ x.val := by
      intro h
      apply hx
      rw [← ZMod.val_injective m h]
      exact hbD d hd
    exact per_d (ZMod.val_lt x) (ZMod.val_lt (f d).1) (ZMod.val_lt d) (ZMod.val_lt (f d).2) hdx hbx
      (hint d hd) (gf_nonneg m _) (gf_ge1 m _) (gf_ge2 m _)
  -- `b` permutes `D`
  have hinj : Set.InjOn (fun d => (f d).1) (D : Set (ZMod m)) :=
    fun d₁ h₁ d₂ h₂ he => hbinj d₁ h₁ d₂ h₂ he
  have himg : D.image (fun d => (f d).1) = D := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
      exact hbD d hd
    · exact (Finset.card_image_of_injOn hinj).ge
  have hperm : ∑ d ∈ D, pf m x (f d).1 = ∑ d ∈ D, pf m x d := by
    calc ∑ d ∈ D, pf m x (f d).1 = ∑ y ∈ D.image (fun d => (f d).1), pf m x y :=
          (Finset.sum_image hinj).symm
      _ = ∑ y ∈ D, pf m x y := by rw [himg]
  -- `Σ g (c d) ≤ 2 Σ g`
  have hgsum : ∑ d ∈ D, gf m (f d).2 ≤ 2 * ∑ y ∈ D, gf m y := by
    calc ∑ d ∈ D, gf m (f d).2
        = ∑ y ∈ D, ∑ d ∈ D.filter (fun d => (f d).2 = y), gf m y :=
          (Finset.sum_fiberwise_of_maps_to' hcD (fun y => gf m y)).symm
      _ ≤ ∑ y ∈ D, 2 * gf m y := by
          apply Finset.sum_le_sum
          intro y _
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcfib y) (gf_nonneg m y)
      _ = 2 * ∑ y ∈ D, gf m y := by rw [Finset.mul_sum]
  -- at most `4 ℓ` points without wrap-around
  set L := D.filter (fun d => d.val ∉ A) with hL
  set NW := D.filter (fun d => (f d).1.val + d.val = x.val + (f d).2.val) with hNW
  have hcover : NW ⊆ L ∪ (D.filter (fun d => (f d).1 ∈ L) ∪ D.filter (fun d => (f d).2 ∈ L)) := by
    intro d hd
    obtain ⟨hdD, heq⟩ := Finset.mem_filter.mp hd
    by_contra hnot
    have hdA : d.val ∈ A := by
      by_contra h
      exact hnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hdD, h⟩))
    have hbA : (f d).1.val ∈ A := by
      by_contra h
      exact hnot (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hdD, Finset.mem_filter.mpr ⟨hbD d hdD, h⟩⟩)))
    have hcA : (f d).2.val ∈ A := by
      by_contra h
      exact hnot (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hdD, Finset.mem_filter.mpr ⟨hcD d hdD, h⟩⟩)))
    rcases hA _ (mem_coe.mpr hbA) _ (mem_coe.mpr hxA) _ (mem_coe.mpr hdA) _ (mem_coe.mpr hcA)
      heq with ⟨e1, -⟩ | ⟨-, e2⟩
    · apply hx
      rw [← ZMod.val_injective m e1]
      exact hbD d hdD
    · apply hx
      rw [← ZMod.val_injective m e2]
      exact hdD
  have hc1 : (D.filter (fun d => (f d).1 ∈ L)).card ≤ L.card :=
    Finset.card_le_card_of_injOn (fun d => (f d).1) (fun d hd => (Finset.mem_filter.mp hd).2)
      (fun d₁ h₁ d₂ h₂ he =>
        hbinj d₁ (Finset.mem_filter.mp h₁).1 d₂ (Finset.mem_filter.mp h₂).1 he)
  have hc2 : (D.filter (fun d => (f d).2 ∈ L)).card ≤ 2 * L.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun d => (f d).2)
      (s := D.filter (fun d => (f d).2 ∈ L)) (t := L)
      (fun d hd => (Finset.mem_filter.mp hd).2)]
    calc ∑ y ∈ L, ((D.filter (fun d => (f d).2 ∈ L)).filter (fun d => (f d).2 = y)).card
        ≤ ∑ y ∈ L, 2 := by
          apply Finset.sum_le_sum
          intro y _
          refine le_trans (Finset.card_le_card ?_) (hcfib y)
          intro d hd
          rw [Finset.mem_filter, Finset.mem_filter] at hd
          exact Finset.mem_filter.mpr ⟨hd.1.1, hd.2⟩
      _ = 2 * L.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hN : NW.card ≤ 4 * L.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le L (D.filter (fun d => (f d).1 ∈ L) ∪
      D.filter (fun d => (f d).2 ∈ L))
    have h3 := Finset.card_union_le (D.filter (fun d => (f d).1 ∈ L))
      (D.filter (fun d => (f d).2 ∈ L))
    omega
  -- summing the pointwise inequality
  have F1 : ∑ d ∈ D, (m : ℤ) ≤ ∑ d ∈ D, (4 * m *
      (if (f d).1.val + d.val = x.val + (f d).2.val then (1 : ℤ) else 0) +
        2 * (pf m x d + pf m x (f d).1) + gf m (f d).2) := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at F1
  have e0 : ∑ d ∈ D, (m : ℤ) = (m : ℤ) * D.card := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have eX : ∑ d ∈ D, 4 * (m : ℤ) *
      (if (f d).1.val + d.val = x.val + (f d).2.val then (1 : ℤ) else 0) =
        4 * (m : ℤ) * (NW.card : ℤ) := by
    simp only [← Finset.mul_sum, Finset.sum_boole, hNW]
  have eY : ∑ d ∈ D, 2 * (pf m x d + pf m x (f d).1) = 4 * ∑ d ∈ D, pf m x d := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hperm]
    ring
  have h4 : (NW.card : ℤ) ≤ 4 * L.card := by exact_mod_cast hN
  have key : 4 * (m : ℤ) * (NW.card : ℤ) ≤ 16 * m * (L.card : ℤ) := by
    have hm : (0 : ℤ) ≤ 4 * m := by positivity
    calc 4 * (m : ℤ) * (NW.card : ℤ) ≤ 4 * m * (4 * L.card) := mul_le_mul_of_nonneg_left h4 hm
      _ = 16 * m * (L.card : ℤ) := by ring
  rw [e0, eX, eY] at F1
  linarith

end OMA.P11Erdos30

theorem OMA.solution : OMA.R_Erdos30_erdos_30_R1_H2_R1.H1 := by
  intro m _ D A x hD hfull hA hx hxA
  exact OMA.P11Erdos30.main_bound m D A x hD hfull hA hx hxA
