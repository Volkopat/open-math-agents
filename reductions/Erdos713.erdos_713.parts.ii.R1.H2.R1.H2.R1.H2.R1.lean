import OMAReductions.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1

/-!
# Reduction Erdos713.erdos_713.parts.ii.R1.H2.R1.H2.R1.H2.R1

Splits the rational-exponent range `α ∈ (3/2, 2)` of Erdős Problem 713(ii) cleanly at `α = 5/3`:

1. **Lower bound (`E713Brown`)**: For every odd prime `p ≥ 5` and `d ∈ ZMod p` with `-d` non-square,
   Brown's unit-sphere graph on `(ZMod p)^3` (`u ~ v ↔ u ≠ v ∧ ‖u - v‖² = d`) is `K_{3,3}`-free
   (proved directly via the vector cross/triple product and the non-square identity
   `(a y - b x)² + c² d = 0`) and has minimum degree at least `p² - 3p` (proved via stereographic
   projection from a point `(x₀, y₀, 0)` on the sphere). Bertrand's postulate on `⌊n^(1/3)⌋` and
   `E713Amplify.padding` yield `n^(5/3) = O(extremalNumber n F)` whenever `K_{3,3} ⊑ F`.
2. **Upper bound (`E713Triples`)**: Dependent Random Choice for triples (`r = 3`, Alon–Krivelevich–Sudakov):
   any `n`-vertex graph with `(2e)³ > n⁵ (s³ + s)` contains a subset `A` of size at least `s` whose
   every triple has at least `s` common neighbors. Embedding the opposite side in `A` and reusing
   `E713Pairs.distinct_choices` gives `extremalNumber n F = O(n^(5/3))` whenever `F` is bipartite
   with all vertices on one side of degree at most `3`.
3. **Exact `Θ(n^(5/3))` and split at `5/3`**: Combining both bounds rules out `α < 5/3` when
   `K_{3,3} ⊑ G` and rules out `α > 5/3` when one side has maximum degree at most `3`; at `α = 5/3`
   the exponent is rational.

References:
- W. G. Brown, On graphs that do not contain a Thomsen graph, Canad. Math. Bull. 9 (1966), 281–285.
- N. Alon, M. Krivelevich, B. Sudakov, Turán numbers of bipartite graphs and related Ramsey-type
  questions, Combin. Probab. Comput. 12 (2003), 477–494.
-/

-- Credit: @sanchan

section

open SimpleGraph Finset
open scoped Classical

namespace E713Brown

lemma two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
  omega

lemma exists_neg_nonsquare (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    ∃ d : ZMod p, d ≠ 0 ∧ ∀ x : ZMod p, x ^ 2 ≠ -d := by
  let S : Finset (ZMod p) := Finset.univ.image (fun x : ZMod p => x ^ 2)
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp3
  have hne : (1 : ZMod p) ≠ -1 := by
    intro h
    apply h2ne
    linear_combination h
  have hlt : S.card < (Finset.univ : Finset (ZMod p)).card := by
    refine lt_of_le_of_ne Finset.card_image_le ?_
    intro heq
    have hinj := (Finset.card_image_iff (f := fun x : ZMod p => x ^ 2) (s := Finset.univ)).mp heq
    have h1 := hinj (Finset.mem_univ (1 : ZMod p)) (Finset.mem_univ (-1 : ZMod p)) (by ring)
    exact hne h1
  obtain ⟨c, _, hcS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hcS (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by ring⟩)
  refine ⟨-c, neg_ne_zero.mpr hc0, fun x hx => hcS ?_⟩
  rw [neg_neg] at hx
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩

lemma exists_sum_two_sq (p : ℕ) [Fact p.Prime] (d : ZMod p) :
    ∃ x₀ y₀ : ZMod p, x₀ ^ 2 + y₀ ^ 2 = d := by
  let S : Finset (ZMod p) := Finset.univ.image (fun x : ZMod p => x ^ 2)
  have h0S : (0 : ZMod p) ∈ S := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by ring⟩
  have hcard : p + 1 ≤ 2 * S.card := by
    have hfib : (Finset.univ : Finset (ZMod p)).card =
        ∑ s ∈ S, (Finset.univ.filter (fun x : ZMod p => x ^ 2 = s)).card :=
      Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))
    have h0fib : (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 0)).card = 1 := by
      have heq : Finset.univ.filter (fun x : ZMod p => x ^ 2 = 0) = {(0 : ZMod p)} := by
        ext x; simp
      rw [heq, Finset.card_singleton]
    have hle2 : ∀ s ∈ S.erase 0, (Finset.univ.filter (fun x : ZMod p => x ^ 2 = s)).card ≤ 2 := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hs)
      have hsub : Finset.univ.filter (fun x : ZMod p => x ^ 2 = a ^ 2) ⊆ ({a, -a} : Finset (ZMod p)) := by
        intro x hx
        have hsq : (x - a) * (x + a) = 0 := by
          have := (Finset.mem_filter.mp hx).2
          linear_combination this
        rcases mul_eq_zero.mp hsq with h1 | h2
        · exact Finset.mem_insert.mpr (Or.inl (sub_eq_zero.mp h1))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (eq_neg_of_add_eq_zero_left h2)))
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    have hsum_le : ∑ s ∈ S.erase 0, (Finset.univ.filter (fun x : ZMod p => x ^ 2 = s)).card ≤
        2 * (S.erase 0).card := by
      calc ∑ s ∈ S.erase 0, (Finset.univ.filter (fun x : ZMod p => x ^ 2 = s)).card
          ≤ ∑ _s ∈ S.erase 0, 2 := Finset.sum_le_sum hle2
        _ = 2 * (S.erase 0).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← Finset.add_sum_erase _ _ h0S, h0fib] at hfib
    have hp_card : (Finset.univ : Finset (ZMod p)).card = p := by
      rw [Finset.card_univ, ZMod.card p]
    have herase : (S.erase 0).card + 1 = S.card := Finset.card_erase_add_one h0S
    omega
  let T : Finset (ZMod p) := S.image (fun y => d - y)
  have hTcard : T.card = S.card :=
    Finset.card_image_of_injective S (fun _ _ h => sub_right_inj.mp h)
  have hndisj : ¬ Disjoint S T := by
    intro hdisj
    have hu : (S ∪ T).card ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj, hTcard, Finset.card_univ, ZMod.card p] at hu
    omega
  obtain ⟨a, haS, haT⟩ := Finset.not_disjoint_iff.mp hndisj
  obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.mp haS
  obtain ⟨b, hbS, hab⟩ := Finset.mem_image.mp haT
  obtain ⟨y₀, _, rfl⟩ := Finset.mem_image.mp hbS
  exact ⟨x₀, y₀, by linear_combination -hab⟩

lemma no_isotropic_orth {K : Type*} [Field K] {d : K} (hnd : ∀ t : K, t ^ 2 ≠ -d)
    (a b c x y z : K) (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h0 : a ^ 2 + b ^ 2 + c ^ 2 = 0)
    (horth : a * x + b * y + c * z = 0)
    (hsph : x ^ 2 + y ^ 2 + z ^ 2 = d) : False := by
  rcases hne with ha | hb | hc
  · apply hnd ((b * z - c * y) / a)
    field_simp
    linear_combination (y ^ 2 + z ^ 2) * h0 - (b * y + c * z - a * x) * horth - a ^ 2 * hsph
  · apply hnd ((c * x - a * z) / b)
    field_simp
    linear_combination (z ^ 2 + x ^ 2) * h0 - (c * z + a * x - b * y) * horth - b ^ 2 * hsph
  · apply hnd ((a * y - b * x) / c)
    field_simp
    linear_combination (x ^ 2 + y ^ 2) * h0 - (a * x + b * y - c * z) * horth - c ^ 2 * hsph

lemma collinear_of_cross_zero {K : Type*} [Field K]
    (p₁ p₂ p₃ q₁ q₂ q₃ : K) (hp : p₁ ≠ 0 ∨ p₂ ≠ 0 ∨ p₃ ≠ 0)
    (hc1 : p₂ * q₃ - p₃ * q₂ = 0)
    (hc2 : p₃ * q₁ - p₁ * q₃ = 0)
    (hc3 : p₁ * q₂ - p₂ * q₁ = 0) :
    ∃ c : K, q₁ = c * p₁ ∧ q₂ = c * p₂ ∧ q₃ = c * p₃ := by
  rcases hp with h1 | h2 | h3
  · refine ⟨q₁ / p₁, by field_simp, ?_, ?_⟩
    · field_simp; linear_combination hc3
    · field_simp; linear_combination -hc2
  · refine ⟨q₂ / p₂, ?_, by field_simp, ?_⟩
    · field_simp; linear_combination -hc3
    · field_simp; linear_combination hc1
  · refine ⟨q₃ / p₃, ?_, ?_, by field_simp⟩
    · field_simp; linear_combination hc2
    · field_simp; linear_combination -hc1

lemma cross_orth_zero {K : Type*} [Field K]
    (v1x v1y v1z v2x v2y v2z ux uy uz : K)
    (h1 : ux * v1x + uy * v1y + uz * v1z = 0)
    (h2 : ux * v2x + uy * v2y + uz * v2z = 0) :
    (v1z * v2x - v1x * v2z) * uz - (v1x * v2y - v1y * v2x) * uy = 0 ∧
    (v1x * v2y - v1y * v2x) * ux - (v1y * v2z - v1z * v2y) * uz = 0 ∧
    (v1y * v2z - v1z * v2y) * uy - (v1z * v2x - v1x * v2z) * ux = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination v2x * h1 - v1x * h2
  · linear_combination v2y * h1 - v1y * h2
  · linear_combination v2z * h1 - v1z * h2

/-- Brown's unit-sphere graph over `K³` (`char K ≠ 2`, `-d` non-square) is `K_{3,3}`-free. -/
theorem sphere_k33_free {K : Type*} [Field K] (h2ne : (2 : K) ≠ 0)
    {d : K} (hnd : ∀ t : K, t ^ 2 ≠ -d)
    (G : SimpleGraph (K × K × K))
    (hadj : ∀ u v : K × K × K, G.Adj u v →
      (u.1 - v.1) ^ 2 + (u.2.1 - v.2.1) ^ 2 + (u.2.2 - v.2.2) ^ 2 = d) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Free G := by
  rintro ⟨e⟩
  have hedge : ∀ (i j : Fin 3),
      ((e (Sum.inl i)).1 - (e (Sum.inr j)).1) ^ 2 +
      ((e (Sum.inl i)).2.1 - (e (Sum.inr j)).2.1) ^ 2 +
      ((e (Sum.inl i)).2.2 - (e (Sum.inr j)).2.2) ^ 2 = d := fun i j =>
    hadj _ _ (e.toHom.map_rel' (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inl i) (Sum.inr j) from Or.inl ⟨rfl, rfl⟩))
  let a0 := e (Sum.inl 0); let a1 := e (Sum.inl 1); let a2 := e (Sum.inl 2)
  let b0 := e (Sum.inr 0); let b1 := e (Sum.inr 1); let b2 := e (Sum.inr 2)
  have ha01 : a0 ≠ a1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (Sum.inl.inj (e.injective h))
  have ha02 : a0 ≠ a2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (Sum.inl.inj (e.injective h))
  have ha12 : a1 ≠ a2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (Sum.inl.inj (e.injective h))
  have hb01 : b0 ≠ b1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (Sum.inr.inj (e.injective h))
  have hb02 : b0 ≠ b2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (Sum.inr.inj (e.injective h))
  have hb12 : b1 ≠ b2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (Sum.inr.inj (e.injective h))
  -- Translate by `a0`
  let u1x := a1.1 - a0.1; let u1y := a1.2.1 - a0.2.1; let u1z := a1.2.2 - a0.2.2
  let u2x := a2.1 - a0.1; let u2y := a2.2.1 - a0.2.1; let u2z := a2.2.2 - a0.2.2
  let w0x := b0.1 - a0.1; let w0y := b0.2.1 - a0.2.1; let w0z := b0.2.2 - a0.2.2
  let w1x := b1.1 - a0.1; let w1y := b1.2.1 - a0.2.1; let w1z := b1.2.2 - a0.2.2
  let w2x := b2.1 - a0.1; let w2y := b2.2.1 - a0.2.1; let w2z := b2.2.2 - a0.2.2
  let v1x := w1x - w0x; let v1y := w1y - w0y; let v1z := w1z - w0z
  let v2x := w2x - w0x; let v2y := w2y - w0y; let v2z := w2z - w0z
  have hw0 : w0x ^ 2 + w0y ^ 2 + w0z ^ 2 = d := by linear_combination hedge 0 0
  have hw1 : w1x ^ 2 + w1y ^ 2 + w1z ^ 2 = d := by linear_combination hedge 0 1
  have hw2 : w2x ^ 2 + w2y ^ 2 + w2z ^ 2 = d := by linear_combination hedge 0 2
  have h10 : (u1x - w0x) ^ 2 + (u1y - w0y) ^ 2 + (u1z - w0z) ^ 2 = d := by
    have := hedge 1 0; linear_combination this
  have h11 : (u1x - w1x) ^ 2 + (u1y - w1y) ^ 2 + (u1z - w1z) ^ 2 = d := by
    have := hedge 1 1; linear_combination this
  have h12 : (u1x - w2x) ^ 2 + (u1y - w2y) ^ 2 + (u1z - w2z) ^ 2 = d := by
    have := hedge 1 2; linear_combination this
  have h20 : (u2x - w0x) ^ 2 + (u2y - w0y) ^ 2 + (u2z - w0z) ^ 2 = d := by
    have := hedge 2 0; linear_combination this
  have h21 : (u2x - w1x) ^ 2 + (u2y - w1y) ^ 2 + (u2z - w1z) ^ 2 = d := by
    have := hedge 2 1; linear_combination this
  have h22 : (u2x - w2x) ^ 2 + (u2y - w2y) ^ 2 + (u2z - w2z) ^ 2 = d := by
    have := hedge 2 2; linear_combination this
  have hd_u1w0 : 2 * (u1x * w0x + u1y * w0y + u1z * w0z) = u1x ^ 2 + u1y ^ 2 + u1z ^ 2 := by
    linear_combination hw0 - h10
  have hd_u2w0 : 2 * (u2x * w0x + u2y * w0y + u2z * w0z) = u2x ^ 2 + u2y ^ 2 + u2z ^ 2 := by
    linear_combination hw0 - h20
  have ho11 : u1x * v1x + u1y * v1y + u1z * v1z = 0 := by
    apply (mul_eq_zero.mp (show 2 * (u1x * v1x + u1y * v1y + u1z * v1z) = 0 by
      linear_combination hw1 - h11 - (hw0 - h10))).resolve_left h2ne
  have ho12 : u1x * v2x + u1y * v2y + u1z * v2z = 0 := by
    apply (mul_eq_zero.mp (show 2 * (u1x * v2x + u1y * v2y + u1z * v2z) = 0 by
      linear_combination hw2 - h12 - (hw0 - h10))).resolve_left h2ne
  have ho21 : u2x * v1x + u2y * v1y + u2z * v1z = 0 := by
    apply (mul_eq_zero.mp (show 2 * (u2x * v1x + u2y * v1y + u2z * v1z) = 0 by
      linear_combination hw1 - h21 - (hw0 - h20))).resolve_left h2ne
  have ho22 : u2x * v2x + u2y * v2y + u2z * v2z = 0 := by
    apply (mul_eq_zero.mp (show 2 * (u2x * v2x + u2y * v2y + u2z * v2z) = 0 by
      linear_combination hw2 - h22 - (hw0 - h20))).resolve_left h2ne
  have hv1_eq : v1x ^ 2 + v1y ^ 2 + v1z ^ 2 + 2 * (w0x * v1x + w0y * v1y + w0z * v1z) = 0 := by
    linear_combination hw1 - hw0
  have hv2_eq : v2x ^ 2 + v2y ^ 2 + v2z ^ 2 + 2 * (w0x * v2x + w0y * v2y + w0z * v2z) = 0 := by
    linear_combination hw2 - hw0
  have hv1_ne : v1x ≠ 0 ∨ v1y ≠ 0 ∨ v1z ≠ 0 := by
    by_contra h; push Not at h
    apply hb01
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · linear_combination -h.1
    · linear_combination -h.2.1
    · linear_combination -h.2.2
  have hu1_ne : u1x ≠ 0 ∨ u1y ≠ 0 ∨ u1z ≠ 0 := by
    by_contra h; push Not at h
    apply ha01
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · linear_combination -h.1
    · linear_combination -h.2.1
    · linear_combination -h.2.2
  let nx := v1y * v2z - v1z * v2y
  let ny := v1z * v2x - v1x * v2z
  let nz := v1x * v2y - v1y * v2x
  by_cases hn : nx = 0 ∧ ny = 0 ∧ nz = 0
  · -- Subcase A: v1, v2 collinear
    obtain ⟨c, hc1, hc2, hc3⟩ := collinear_of_cross_zero v1x v1y v1z v2x v2y v2z hv1_ne hn.1 hn.2.1 hn.2.2
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hb02
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · linear_combination -hc1
      · linear_combination -hc2
      · linear_combination -hc3
    have hc1' : c ≠ 1 := by
      rintro rfl; apply hb12
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · linear_combination -hc1
      · linear_combination -hc2
      · linear_combination -hc3
    have hprod : c * (c - 1) * (v1x ^ 2 + v1y ^ 2 + v1z ^ 2) = 0 := by
      linear_combination hv2_eq - c * hv1_eq - (v2x + c * v1x + 2 * w0x) * hc1 -
        (v2y + c * v1y + 2 * w0y) * hc2 - (v2z + c * v1z + 2 * w0z) * hc3
    have hv1_iso : v1x ^ 2 + v1y ^ 2 + v1z ^ 2 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hc0 (sub_ne_zero.mpr hc1'))
    have hv1_orth : v1x * w0x + v1y * w0y + v1z * w0z = 0 :=
      (mul_eq_zero.mp (show 2 * (v1x * w0x + v1y * w0y + v1z * w0z) = 0 by
        linear_combination hv1_eq - hv1_iso)).resolve_left h2ne
    exact no_isotropic_orth hnd v1x v1y v1z w0x w0y w0z hv1_ne hv1_iso hv1_orth hw0
  · -- Subcase B: n = v1 × v2 ≠ 0, so u1 and u2 are both scalar multiples of n
    have hn_ne : nx ≠ 0 ∨ ny ≠ 0 ∨ nz ≠ 0 := by
      by_contra h
      push Not at h
      exact hn ⟨h.1, h.2.1, h.2.2⟩
    have hu1_cross : ny * u1z - nz * u1y = 0 ∧ nz * u1x - nx * u1z = 0 ∧ nx * u1y - ny * u1x = 0 :=
      cross_orth_zero v1x v1y v1z v2x v2y v2z u1x u1y u1z ho11 ho12
    have hu2_cross : ny * u2z - nz * u2y = 0 ∧ nz * u2x - nx * u2z = 0 ∧ nx * u2y - ny * u2x = 0 :=
      cross_orth_zero v1x v1y v1z v2x v2y v2z u2x u2y u2z ho21 ho22
    obtain ⟨α, hα1, hα2, hα3⟩ := collinear_of_cross_zero nx ny nz u1x u1y u1z hn_ne
      hu1_cross.1 hu1_cross.2.1 hu1_cross.2.2
    obtain ⟨β, hβ1, hβ2, hβ3⟩ := collinear_of_cross_zero nx ny nz u2x u2y u2z hn_ne
      hu2_cross.1 hu2_cross.2.1 hu2_cross.2.2
    have hα0 : α ≠ 0 := by
      rintro rfl; apply ha01
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · linear_combination -hα1
      · linear_combination -hα2
      · linear_combination -hα3
    have hβ0 : β ≠ 0 := by
      rintro rfl; apply ha02
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · linear_combination -hβ1
      · linear_combination -hβ2
      · linear_combination -hβ3
    have hαβ : α ≠ β := by
      rintro rfl; apply ha12
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · linear_combination hα1 - hβ1
      · linear_combination hα2 - hβ2
      · linear_combination hα3 - hβ3
    let c := β / α
    have hc0 : c ≠ 0 := div_ne_zero hβ0 hα0
    have hc1' : c ≠ 1 := fun h => hαβ ((div_eq_one_iff_eq hα0).mp h).symm
    have hcu1 : u2x = c * u1x := by dsimp [c]; field_simp; linear_combination α * hβ1 - β * hα1
    have hcu2 : u2y = c * u1y := by dsimp [c]; field_simp; linear_combination α * hβ2 - β * hα2
    have hcu3 : u2z = c * u1z := by dsimp [c]; field_simp; linear_combination α * hβ3 - β * hα3
    have hprod : c * (c - 1) * (u1x ^ 2 + u1y ^ 2 + u1z ^ 2) = 0 := by
      rw [hcu1, hcu2, hcu3] at hd_u2w0
      linear_combination c * hd_u1w0 - hd_u2w0
    have hu1_iso : u1x ^ 2 + u1y ^ 2 + u1z ^ 2 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hc0 (sub_ne_zero.mpr hc1'))
    have hu1_orth : u1x * w0x + u1y * w0y + u1z * w0z = 0 :=
      (mul_eq_zero.mp (show 2 * (u1x * w0x + u1y * w0y + u1z * w0z) = 0 by
        linear_combination hd_u1w0 + hu1_iso)).resolve_left h2ne
    exact no_isotropic_orth hnd u1x u1y u1z w0x w0y w0z hu1_ne hu1_iso hu1_orth hw0

/-- Brown's `K_{3,3}`-free graph on `(ZMod p)³` has at least `p³ (p² - 3p) / 2` edges. -/
theorem brown_witness (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∃ G : SimpleGraph (ZMod p × ZMod p × ZMod p),
      (completeBipartiteGraph (Fin 3) (Fin 3)).Free G ∧
      p ^ 3 * (p ^ 2 - 3 * p) ≤ 2 * G.edgeFinset.card := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p (by omega)
  obtain ⟨d, hd0, hnd⟩ := exists_neg_nonsquare p (by omega)
  obtain ⟨x₀, y₀, hxy0⟩ := exists_sum_two_sq p d
  have hxy_ne : x₀ ≠ 0 ∨ y₀ ≠ 0 := by
    by_contra h; push Not at h
    apply hd0
    linear_combination -hxy0 + x₀ * h.1 + y₀ * h.2
  let G : SimpleGraph (ZMod p × ZMod p × ZMod p) := {
    Adj u v := u ≠ v ∧ (u.1 - v.1) ^ 2 + (u.2.1 - v.2.1) ^ 2 + (u.2.2 - v.2.2) ^ 2 = d
    symm := ⟨fun u v h => ⟨h.1.symm, by linear_combination h.2⟩⟩
    loopless := ⟨fun u h => h.1 rfl⟩ }
  refine ⟨G, sphere_k33_free h2ne hnd G (fun _ _ h => h.2), ?_⟩
  let S : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter (fun ab => ab.1 ^ 2 + ab.2 ^ 2 + 1 ≠ 0 ∧ x₀ * ab.1 + y₀ * ab.2 ≠ 0)
  have hScard : p ^ 2 - 3 * p ≤ S.card := by
    let B1 : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun ab => x₀ * ab.1 + y₀ * ab.2 = 0)
    let B2 : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun ab => ab.1 ^ 2 + ab.2 ^ 2 + 1 = 0)
    have hB1 : B1.card ≤ p := by
      rcases hxy_ne with hx0 | hy0
      · have hinj : Set.InjOn Prod.snd (B1 : Set (ZMod p × ZMod p)) := by
          intro u hu v hv hEq
          have hu' : x₀ * u.1 + y₀ * u.2 = 0 := (Finset.mem_filter.mp hu).2
          have hv' : x₀ * v.1 + y₀ * v.2 = 0 := (Finset.mem_filter.mp hv).2
          have hx : u.1 = v.1 := by
            apply sub_eq_zero.mp
            apply (mul_eq_zero.mp (show x₀ * (u.1 - v.1) = 0 by
              linear_combination hu' - hv' - y₀ * hEq)).resolve_left hx0
          exact Prod.ext hx hEq
        calc B1.card = (B1.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_univ _
          _ = p := by rw [Finset.card_univ, ZMod.card p]
      · have hinj : Set.InjOn Prod.fst (B1 : Set (ZMod p × ZMod p)) := by
          intro u hu v hv hEq
          have hu' : x₀ * u.1 + y₀ * u.2 = 0 := (Finset.mem_filter.mp hu).2
          have hv' : x₀ * v.1 + y₀ * v.2 = 0 := (Finset.mem_filter.mp hv).2
          have hy : u.2 = v.2 := by
            apply sub_eq_zero.mp
            apply (mul_eq_zero.mp (show y₀ * (u.2 - v.2) = 0 by
              linear_combination hu' - hv' - x₀ * hEq)).resolve_left hy0
          exact Prod.ext hEq hy
        calc B1.card = (B1.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_univ _
          _ = p := by rw [Finset.card_univ, ZMod.card p]
    have hB2 : B2.card ≤ 2 * p := by
      have hfib : B2.card = ∑ a : ZMod p, (B2.filter (fun ab => ab.1 = a)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      rw [hfib]
      have hper : ∀ a : ZMod p, (B2.filter (fun ab => ab.1 = a)).card ≤ 2 := by
        intro a
        by_cases hne : (B2.filter (fun ab => ab.1 = a)).Nonempty
        · obtain ⟨⟨a0, b0⟩, hmem⟩ := hne
          have ha0 : a0 = a := (Finset.mem_filter.mp hmem).2
          have hb0 : a ^ 2 + b0 ^ 2 + 1 = 0 := by
            rw [← ha0]; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
          have hsub : B2.filter (fun ab => ab.1 = a) ⊆ ({(a, b0), (a, -b0)} : Finset (ZMod p × ZMod p)) := by
            intro ⟨a', b'⟩ hm
            have ha' : a' = a := (Finset.mem_filter.mp hm).2
            have hb' : a ^ 2 + b' ^ 2 + 1 = 0 := by
              rw [← ha']; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
            have hmul : (b' - b0) * (b' + b0) = 0 := by linear_combination hb' - hb0
            rcases mul_eq_zero.mp hmul with h1 | h2
            · exact Finset.mem_insert.mpr (Or.inl (Prod.ext ha' (sub_eq_zero.mp h1)))
            · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
                (Prod.ext ha' (eq_neg_of_add_eq_zero_left h2))))
          exact (Finset.card_le_card hsub).trans Finset.card_le_two
        · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
      calc ∑ a : ZMod p, (B2.filter (fun ab => ab.1 = a)).card
          ≤ ∑ _a : ZMod p, 2 := Finset.sum_le_sum (fun a _ => hper a)
        _ = 2 * p := by rw [Finset.sum_const, Finset.card_univ, ZMod.card p, smul_eq_mul, mul_comm]
    have hcov : (Finset.univ : Finset (ZMod p × ZMod p)) ⊆ S ∪ B1 ∪ B2 := by
      intro ab _
      by_cases h1 : ab.1 ^ 2 + ab.2 ^ 2 + 1 = 0
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      · by_cases h2 : x₀ * ab.1 + y₀ * ab.2 = 0
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩))
    have htot := Finset.card_le_card hcov
    have hu1 := Finset.card_union_le (S ∪ B1) B2
    have hu2 := Finset.card_union_le S B1
    have huniv : (Finset.univ : Finset (ZMod p × ZMod p)).card = p ^ 2 := by
      rw [Finset.card_univ, Fintype.card_prod, ZMod.card p, sq]
    omega
  have hdeg : ∀ u : ZMod p × ZMod p × ZMod p, p ^ 2 - 3 * p ≤ G.degree u := by
    intro u
    let φ : ZMod p × ZMod p → ZMod p × ZMod p × ZMod p := fun ab =>
      let t := -(2 * (x₀ * ab.1 + y₀ * ab.2)) / (ab.1 ^ 2 + ab.2 ^ 2 + 1)
      (u.1 + x₀ + t * ab.1, u.2.1 + y₀ + t * ab.2, u.2.2 + t)
    have hinj : Set.InjOn φ (S : Set (ZMod p × ZMod p)) := by
      intro ab1 hab1 ab2 hab2 hEq
      have h1 := (Finset.mem_filter.mp hab1).2
      have h2 := (Finset.mem_filter.mp hab2).2
      let t1 := -(2 * (x₀ * ab1.1 + y₀ * ab1.2)) / (ab1.1 ^ 2 + ab1.2 ^ 2 + 1)
      let t2 := -(2 * (x₀ * ab2.1 + y₀ * ab2.2)) / (ab2.1 ^ 2 + ab2.2 ^ 2 + 1)
      have ht1_ne : t1 ≠ 0 := div_ne_zero (neg_ne_zero.mpr (mul_ne_zero h2ne h1.2)) h1.1
      have hEq1 : u.1 + x₀ + t1 * ab1.1 = u.1 + x₀ + t2 * ab2.1 := congrArg Prod.fst hEq
      have hEq2 : u.2.1 + y₀ + t1 * ab1.2 = u.2.1 + y₀ + t2 * ab2.2 := congrArg (fun q => q.2.1) hEq
      have hEq3 : u.2.2 + t1 = u.2.2 + t2 := congrArg (fun q => q.2.2) hEq
      have ht_eq : t1 = t2 := add_left_cancel hEq3
      rw [← ht_eq] at hEq1 hEq2
      have ha_eq : ab1.1 = ab2.1 := mul_left_cancel₀ ht1_ne (add_left_cancel hEq1)
      have hb_eq : ab1.2 = ab2.2 := mul_left_cancel₀ ht1_ne (add_left_cancel hEq2)
      exact Prod.ext ha_eq hb_eq
    have hsub : S.image φ ⊆ G.neighborFinset u := by
      intro w hw
      obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hw
      have hcond := (Finset.mem_filter.mp hab).2
      let t := -(2 * (x₀ * ab.1 + y₀ * ab.2)) / (ab.1 ^ 2 + ab.2 ^ 2 + 1)
      have ht_ne : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr (mul_ne_zero h2ne hcond.2)) hcond.1
      rw [G.mem_neighborFinset]
      refine ⟨?_, ?_⟩
      · intro hEq
        have h3 : u.2.2 = u.2.2 + t := congrArg (fun q => q.2.2) hEq
        exact ht_ne (by linear_combination -h3)
      · change (u.1 - (u.1 + x₀ + t * ab.1)) ^ 2 +
               (u.2.1 - (u.2.1 + y₀ + t * ab.2)) ^ 2 +
               (u.2.2 - (u.2.2 + t)) ^ 2 = d
        have hden : ab.1 ^ 2 + ab.2 ^ 2 + 1 ≠ 0 := hcond.1
        dsimp only [t]
        field_simp
        linear_combination (ab.1 ^ 2 + ab.2 ^ 2 + 1) ^ 2 * hxy0
    calc p ^ 2 - 3 * p ≤ S.card := hScard
      _ = (S.image φ).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (G.neighborFinset u).card := Finset.card_le_card hsub
      _ = G.degree u := G.card_neighborFinset_eq_degree u
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hdeg u)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
      ZMod.card p, smul_eq_mul, G.sum_degrees_eq_twice_card_edges] at hsum
  have hp3 : p * (p * p) = p ^ 3 := by ring
  rw [hp3] at hsum
  convert! hsum using 2
  congr!

lemma k33_no_isolated : ∀ v, ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).IsIsolated v := by
  intro v h
  cases v with
  | inl i => exact h (Sum.inr 0) (Or.inl ⟨rfl, rfl⟩)
  | inr j => exact h (Sum.inl 0) (Or.inr ⟨rfl, rfl⟩)

/-- Uniform lower bound `n⁵ ≤ 128³ * ex(n, K_{3,3})³` for `n ≥ 1000` via Bertrand's postulate. -/
theorem k33_lower_uniform (n : ℕ) (hn : 1000 ≤ n) :
    n ^ 5 ≤ 128 ^ 3 * (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3))) ^ 3 := by
  let S := (Finset.range (n + 1)).filter (fun m => m ^ 3 ≤ n)
  have h0S : 0 ∈ S := by simp [S]
  let k := S.max' ⟨0, h0S⟩
  have hk_mem : k ∈ S := Finset.max'_mem S ⟨0, h0S⟩
  have hk3_le : k ^ 3 ≤ n := (Finset.mem_filter.mp hk_mem).2
  have h10_mem : 10 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩
  have hk10 : 10 ≤ k := Finset.le_max' S 10 h10_mem
  have hlt_succ : n < (k + 1) ^ 3 := by
    by_contra hle
    push Not at hle
    have hk1_le_n : k + 1 ≤ n := by
      have : k + 1 ≤ (k + 1) ^ 3 := Nat.le_self_pow (by omega) _
      omega
    have hk1_mem : k + 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hle⟩
    have := Finset.le_max' S (k + 1) hk1_mem
    omega
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (k / 2) (by omega)
  have hp6 : 6 ≤ p := by omega
  have hpk : p ≤ k := by omega
  have hk_2p : k + 1 ≤ 2 * p := by omega
  have hp3_le_n : p ^ 3 ≤ n := (Nat.pow_le_pow_left hpk 3).trans hk3_le
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨G, hfree, hedges⟩ := brown_witness p (by omega)
  have hcardW : Fintype.card (ZMod p × ZMod p × ZMod p) = p ^ 3 := by
    rw [Fintype.card_prod, Fintype.card_prod, ZMod.card p]; ring
  have hpad : G.edgeFinset.card ≤ extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) :=
    E713Amplify.padding (completeBipartiteGraph (Fin 3) (Fin 3)) k33_no_isolated G hfree n
      (hcardW.le.trans hp3_le_n)
  have hp2_half : p ^ 2 ≤ 2 * (p ^ 2 - 3 * p) := by
    have h6p : 6 * p ≤ p ^ 2 := by nlinarith
    have h3p : 3 * p ≤ p ^ 2 := by omega
    zify [h3p]
    nlinarith
  have hp5_le : p ^ 5 ≤ 4 * extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) := by
    have h1 : p ^ 5 ≤ 2 * (p ^ 3 * (p ^ 2 - 3 * p)) := by
      calc p ^ 5 = p ^ 3 * p ^ 2 := by ring
        _ ≤ p ^ 3 * (2 * (p ^ 2 - 3 * p)) := Nat.mul_le_mul_left _ hp2_half
        _ = 2 * (p ^ 3 * (p ^ 2 - 3 * p)) := by ring
    omega
  have hn_lt : n ≤ 8 * p ^ 3 := by
    have h1 : (k + 1) ^ 3 ≤ (2 * p) ^ 3 := Nat.pow_le_pow_left hk_2p 3
    have h2 : (2 * p) ^ 3 = 8 * p ^ 3 := by ring
    omega
  have hn5 : n ^ 5 ≤ (8 * p ^ 3) ^ 5 := Nat.pow_le_pow_left hn_lt 5
  have hp15 : (p ^ 5) ^ 3 ≤ (4 * extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3))) ^ 3 :=
    Nat.pow_le_pow_left hp5_le 3
  have hid1 : (8 * p ^ 3) ^ 5 = 32768 * (p ^ 5) ^ 3 := by ring
  have hid2 : 32768 * (4 * extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3))) ^ 3 =
      128 ^ 3 * (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3))) ^ 3 := by ring
  calc n ^ 5 ≤ (8 * p ^ 3) ^ 5 := hn5
    _ = 32768 * (p ^ 5) ^ 3 := hid1
    _ ≤ 32768 * (4 * extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3))) ^ 3 :=
        Nat.mul_le_mul_left _ hp15
    _ = 128 ^ 3 * (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3))) ^ 3 := hid2

end E713Brown

end

section

open SimpleGraph Finset
open scoped Classical

namespace E713Triples

lemma cube_sum_le_card_sq_mul_sum_cube {W : Type*} (s : Finset W) (f : W → ℕ) :
    (∑ v ∈ s, f v) ^ 3 ≤ s.card ^ 2 * ∑ v ∈ s, (f v) ^ 3 := by
  have hcs : (∑ v ∈ s, f v) ^ 2 ≤ s.card * ∑ v ∈ s, (f v) ^ 2 :=
    sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  have hcheb : (∑ v ∈ s, (f v) ^ 2) * (∑ v ∈ s, f v) ≤ s.card * ∑ v ∈ s, (f v) ^ 3 := by
    have hpair : ∀ u ∈ s, ∀ v ∈ s,
        (f u) ^ 2 * f v + f u * (f v) ^ 2 ≤ (f u) ^ 3 + (f v) ^ 3 := by
      intro u _ v _
      have h : (0 : ℤ) ≤ ((f u : ℤ) - (f v : ℤ)) ^ 2 * ((f u : ℤ) + (f v : ℤ)) :=
        mul_nonneg (sq_nonneg _) (by positivity)
      have hz : ((f u : ℤ) ^ 2 * (f v : ℤ) + (f u : ℤ) * (f v : ℤ) ^ 2) ≤
          (f u : ℤ) ^ 3 + (f v : ℤ) ^ 3 := by linarith
      exact_mod_cast hz
    have hsum := Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => hpair u hu v hv
    simp_rw [Finset.sum_add_distrib] at hsum
    have h1 : (∑ u ∈ s, ∑ v ∈ s, (f u) ^ 2 * f v) = (∑ u ∈ s, (f u) ^ 2) * (∑ v ∈ s, f v) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => (Finset.mul_sum s f _).symm
    have h2 : (∑ u ∈ s, ∑ v ∈ s, f u * (f v) ^ 2) = (∑ v ∈ s, (f v) ^ 2) * (∑ u ∈ s, f u) := by
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => mul_comm _ _
    have h3 : (∑ u ∈ s, ∑ _v ∈ s, (f u) ^ 3) = s.card * ∑ u ∈ s, (f u) ^ 3 := by
      simp_rw [Finset.sum_const, smul_eq_mul]
      rw [Finset.mul_sum]
    have h4 : (∑ _u ∈ s, ∑ v ∈ s, (f v) ^ 3) = s.card * ∑ v ∈ s, (f v) ^ 3 := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [h1, h2, h3, h4] at hsum
    omega
  calc (∑ v ∈ s, f v) ^ 3 = (∑ v ∈ s, f v) ^ 2 * (∑ v ∈ s, f v) := by ring
    _ ≤ (s.card * ∑ v ∈ s, (f v) ^ 2) * (∑ v ∈ s, f v) := Nat.mul_le_mul_right _ hcs
    _ = s.card * ((∑ v ∈ s, (f v) ^ 2) * (∑ v ∈ s, f v)) := by ring
    _ ≤ s.card * (s.card * ∑ v ∈ s, (f v) ^ 3) := Nat.mul_le_mul_left _ hcheb
    _ = s.card ^ 2 * ∑ v ∈ s, (f v) ^ 3 := by ring

/-- Dependent Random Choice for triples (`r = 3`): finds `A` of size `≥ s` whose every
triple of vertices has at least `s` common neighbors. -/
theorem rich_set_three {W : Type*} [Fintype W] (X : SimpleGraph W) (s : ℕ)
    (dense : (Fintype.card W) ^ 5 * (s ^ 3 + s) < (2 * X.edgeFinset.card) ^ 3) :
    ∃ A : Finset W, s ≤ A.card ∧
      ∀ u₁ ∈ A, ∀ u₂ ∈ A, ∀ u₃ ∈ A,
        s ≤ (X.neighborFinset u₁ ∩ X.neighborFinset u₂ ∩ X.neighborFinset u₃).card := by
  let V := (Finset.univ : Finset W)
  let triples := (Finset.univ : Finset (W × W × W))
  let common (t : W × W × W) :=
    X.neighborFinset t.1 ∩ X.neighborFinset t.2.1 ∩ X.neighborFinset t.2.2
  let bad := triples.filter fun b => (common b).card < s
  let inside (t : W × W × W) :=
    bad.filter fun b => b.1 ∈ common t ∧ b.2.1 ∈ common t ∧ b.2.2 ∈ common t
  have sym (t b : W × W × W) :
      (b.1 ∈ common t ∧ b.2.1 ∈ common t ∧ b.2.2 ∈ common t) ↔
      (t.1 ∈ common b ∧ t.2.1 ∈ common b ∧ t.2.2 ∈ common b) := by
    simp only [common, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨⟨h11, h12⟩, h13⟩, ⟨⟨h21, h22⟩, h23⟩, ⟨⟨h31, h32⟩, h33⟩⟩
      exact ⟨⟨⟨h11.symm, h21.symm⟩, h31.symm⟩, ⟨⟨h12.symm, h22.symm⟩, h32.symm⟩,
        ⟨⟨h13.symm, h23.symm⟩, h33.symm⟩⟩
    · rintro ⟨⟨⟨h11, h12⟩, h13⟩, ⟨⟨h21, h22⟩, h23⟩, ⟨⟨h31, h32⟩, h33⟩⟩
      exact ⟨⟨⟨h11.symm, h21.symm⟩, h31.symm⟩, ⟨⟨h12.symm, h22.symm⟩, h32.symm⟩,
        ⟨⟨h13.symm, h23.symm⟩, h33.symm⟩⟩
  have products (b : W × W × W) :
      (triples.filter fun t => b.1 ∈ common t ∧ b.2.1 ∈ common t ∧ b.2.2 ∈ common t) =
        common b ×ˢ (common b ×ˢ common b) := by
    ext t
    simp only [triples, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, sym t b]
  have total_bad : ∑ t ∈ triples, (inside t).card ≤ (Fintype.card W) ^ 3 * s ^ 3 := by
    simp only [inside, Finset.card_filter]
    rw [Finset.sum_comm]
    have per (b) (hb : b ∈ bad) :
        (∑ t ∈ triples, if b.1 ∈ common t ∧ b.2.1 ∈ common t ∧ b.2.2 ∈ common t then 1 else 0) ≤
          s ^ 3 := by
      rw [← Finset.card_filter, products, Finset.card_product, Finset.card_product]
      have hlt := (Finset.mem_filter.mp hb).2.le
      have hpow : (common b).card * ((common b).card * (common b).card) = (common b).card ^ 3 := by ring
      rw [hpow]
      exact Nat.pow_le_pow_left hlt 3
    apply (Finset.sum_le_sum per).trans
    rw [Finset.sum_const, smul_eq_mul]
    have le : bad.card ≤ (Fintype.card W) ^ 3 := by
      calc bad.card ≤ triples.card := Finset.card_le_univ _
        _ = (Fintype.card W) ^ 3 := by
          simp [triples, Fintype.card_prod]; ring
    exact Nat.mul_le_mul_right _ le
  have fibers (v : W) :
      (triples.filter (fun t => v ∈ common t)) =
        X.neighborFinset v ×ˢ (X.neighborFinset v ×ˢ X.neighborFinset v) := by
    ext t
    simp [triples, common, SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
  have asFilter (t : W × W × W) : common t = V.filter (fun v => v ∈ common t) := by ext v; simp [V]
  have total : (∑ t ∈ triples, (common t).card) = ∑ v : W, (X.degree v) ^ 3 := by
    calc (∑ t ∈ triples, (common t).card)
        = ∑ t ∈ triples, ∑ v ∈ V, if v ∈ common t then 1 else 0 := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← Finset.card_filter, ← asFilter]
      _ = ∑ v ∈ V, (X.degree v) ^ 3 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [← Finset.card_filter, fibers, Finset.card_product, Finset.card_product,
              X.card_neighborFinset_eq_degree]
          ring
  have hcs := cube_sum_le_card_sq_mul_sum_cube (s := (Finset.univ : Finset W)) (f := fun v => X.degree v)
  rw [Finset.card_univ, X.sum_degrees_eq_twice_card_edges, ← total] at hcs
  have existsTriple : ∃ t ∈ triples, (inside t).card + s < (common t).card := by
    by_contra! all
    have cap := Finset.sum_le_sum all
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at cap
    have hn3 : triples.card = (Fintype.card W) ^ 3 := by
      simp [triples, Fintype.card_prod]; ring
    rw [hn3] at cap
    have hbound : ∑ t ∈ triples, (common t).card ≤ (Fintype.card W) ^ 3 * (s ^ 3 + s) := by
      have h1 : (∑ t ∈ triples, (inside t).card) + (Fintype.card W) ^ 3 * s ≤
          (Fintype.card W) ^ 3 * s ^ 3 + (Fintype.card W) ^ 3 * s :=
        Nat.add_le_add_right total_bad _
      have h2 : (Fintype.card W) ^ 3 * s ^ 3 + (Fintype.card W) ^ 3 * s =
          (Fintype.card W) ^ 3 * (s ^ 3 + s) := by ring
      omega
    have hmul := Nat.mul_le_mul_left ((Fintype.card W) ^ 2) hbound
    have hid : (Fintype.card W) ^ 2 * ((Fintype.card W) ^ 3 * (s ^ 3 + s)) =
        (Fintype.card W) ^ 5 * (s ^ 3 + s) := by ring
    omega
  obtain ⟨t, _, ht⟩ := existsTriple
  let D := (inside t).image Prod.fst
  let A := common t \ D
  have fit : s ≤ A.card := by
    have hD : D.card ≤ (inside t).card := Finset.card_image_le
    have loss := Finset.le_card_sdiff D (common t)
    dsimp [A]
    omega
  refine ⟨A, fit, ?_⟩
  intro u₁ hu₁ u₂ hu₂ u₃ hu₃
  by_contra! few
  have fb : (u₁, u₂, u₃) ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, few⟩
  have finside : (u₁, u₂, u₃) ∈ inside t := Finset.mem_filter.mpr
    ⟨fb, (Finset.mem_sdiff.mp hu₁).1, (Finset.mem_sdiff.mp hu₂).1, (Finset.mem_sdiff.mp hu₃).1⟩
  exact (Finset.mem_sdiff.mp hu₁).2 (Finset.mem_image.mpr ⟨(u₁, u₂, u₃), finside, rfl⟩)

lemma subset_triple_of_card_le_three {W : Type*} [DecidableEq W] {A T : Finset W}
    (hTA : T ⊆ A) (hcard : T.card ≤ 3) (hne : A.Nonempty) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, T ⊆ {a, b, c} := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hcases : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 ∨ T.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · rw [Finset.card_eq_zero.mp h0]
    exact ⟨x₀, hx₀, x₀, hx₀, x₀, hx₀, Finset.empty_subset _⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    have ha : a ∈ A := hTA (Finset.mem_singleton_self a)
    exact ⟨a, ha, a, ha, a, ha, by intro z hz; simp_all⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h2
    have ha : a ∈ A := hTA (by simp)
    have hb : b ∈ A := hTA (by simp)
    exact ⟨a, ha, b, hb, b, hb, by intro z hz; simp_all⟩
  · obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp h3
    have ha : a ∈ A := hTA (by simp)
    have hb : b ∈ A := hTA (by simp)
    have hc : c ∈ A := hTA (by simp)
    exact ⟨a, ha, b, hb, c, hc, subset_rfl⟩

/-- Embed a bipartite graph `F` with maximum degree at most `3` on `Rᶜ` into `X`. -/
theorem embed_three {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V) (A : Finset W)
    (colors : ∀ u v, F.Adj u v → (u ∈ R ↔ v ∉ R)) (left : ∀ v ∉ R, F.degree v ≤ 3)
    (hne : A.Nonempty) (fit : Fintype.card V ≤ A.card)
    (rich : ∀ u₁ ∈ A, ∀ u₂ ∈ A, ∀ u₃ ∈ A,
      Fintype.card V ≤ (X.neighborFinset u₁ ∩ X.neighborFinset u₂ ∩ X.neighborFinset u₃).card) :
    F ⊑ X := by
  let L := Rᶜ
  let inj : R ↪ A := R.equivFin.toEmbedding.trans
    ((Fin.castLEEmb ((Finset.card_le_univ R).trans fit)).trans A.equivFin.symm.toEmbedding)
  let f : R ↪ W := inj.trans (Function.Embedding.subtype _)
  let D := Finset.univ.map f
  let ns (v : L) := Finset.univ.filter fun x : R => F.Adj v.val x.val
  have neighbors (v : L) : ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, (ns v).map f ⊆ {a, b, c} := by
    have inside : (ns v).map f ⊆ A := by
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
      exact (inj i).property
    have sub : (ns v).map (Function.Embedding.subtype _) ⊆ F.neighborFinset v.val := by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
      exact (F.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hi).2
    have size := Finset.card_le_card sub
    rw [Finset.card_map, F.card_neighborFinset_eq_degree] at size
    have cap : ((ns v).map f).card ≤ 3 := by
      rw [Finset.card_map]
      exact size.trans (left v.val (Finset.mem_compl.mp v.property))
    exact subset_triple_of_card_le_three inside cap hne
  choose a ha b hb c hc adj using neighbors
  let opts (v : L) := X.neighborFinset (a v) ∩ X.neighborFinset (b v) ∩ X.neighborFinset (c v)
  have total : D.card + Fintype.card L = Fintype.card V := by
    simp [D, L, Nat.add_sub_of_le (Finset.card_le_univ R)]
  have many (v : L) : D.card + Fintype.card L ≤ (opts v).card := by
    rw [total]
    exact rich _ (ha v) _ (hb v) _ (hc v)
  obtain ⟨g, valid⟩ := E713Pairs.distinct_choices D opts many
  have link (u : L) (v : R) (h : F.Adj u.val v.val) : X.Adj (g u) (f v) := by
    have mapped : f v ∈ (ns u).map f :=
      Finset.mem_map.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
    have hv := adj u mapped
    have hg := (valid u).1
    simp only [opts, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with he | he | he
    · rw [he]; exact hg.1.1.symm
    · rw [he]; exact hg.1.2.symm
    · rw [he]; exact hg.2.symm
  let h (v : V) := if mem : v ∈ R then f ⟨v, mem⟩ else g ⟨v, Finset.mem_compl.mpr mem⟩
  refine ⟨⟨⟨h, ?_⟩, ?_⟩⟩
  · intro u v edge
    by_cases hu : u ∈ R
    · have hv := (colors u v edge).mp hu
      simpa [h, hu, hv] using (link ⟨v, Finset.mem_compl.mpr hv⟩ ⟨u, hu⟩ edge.symm).symm
    · have hv := (colors v u edge.symm).mpr hu
      simpa [h, hu, hv] using link ⟨u, Finset.mem_compl.mpr hu⟩ ⟨v, hv⟩ edge
  · intro u v eq
    change h u = h v at eq
    have apart (x : R) (y : L) : f x ≠ g y :=
      fun he => (valid y).2 (Finset.mem_map.mpr ⟨x, Finset.mem_univ _, he⟩)
    by_cases hu : u ∈ R <;> by_cases hv : v ∈ R
    · exact congrArg Subtype.val (f.injective (by simpa [h, hu, hv] using eq : f ⟨u, hu⟩ = f ⟨v, hv⟩))
    · exact (apart ⟨u, hu⟩ ⟨v, Finset.mem_compl.mpr hv⟩ (by simpa [h, hu, hv] using eq)).elim
    · exact (apart ⟨v, hv⟩ ⟨u, Finset.mem_compl.mpr hu⟩ (by simpa [h, hu, hv] using eq.symm)).elim
    · exact congrArg Subtype.val (g.injective (by simpa [h, hu, hv] using eq :
        g ⟨u, Finset.mem_compl.mpr hu⟩ = g ⟨v, Finset.mem_compl.mpr hv⟩))

theorem degree_three_bound {V : Type*} [Fintype V] [DecidableEq V] (F : SimpleGraph V)
    (R : Finset V) (colors : ∀ u v, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (left : ∀ v ∉ R, F.degree v ≤ 3) (n : ℕ) (nonemptyEdges : F ≠ ⊥) :
    (2 * extremalNumber n F) ^ 3 ≤ n ^ 5 * ((Fintype.card V) ^ 3 + Fintype.card V) := by
  have witness : ∃ X : SimpleGraph (Fin n), F.Free X ∧ X.edgeFinset.card = extremalNumber n F := by
    obtain ⟨X, _, ext⟩ := exists_isExtremal_free (V := Fin n) nonemptyEdges
    obtain ⟨avoid, h⟩ := isExtremal_free_iff.mp ext
    refine ⟨X, avoid, ?_⟩
    convert! h using 1
    · congr! 2
    · rw [Fintype.card_fin]
  obtain ⟨X, avoid, edges⟩ := witness
  by_contra! dense
  rw [← edges] at dense
  have h : (Fintype.card (Fin n)) ^ 5 * ((Fintype.card V) ^ 3 + Fintype.card V) <
      (2 * X.edgeFinset.card) ^ 3 := by
    simpa only [Fintype.card_fin] using dense
  obtain ⟨A, fit, rich⟩ := rich_set_three X (Fintype.card V) h
  obtain ⟨u, v, edge⟩ := ne_bot_iff_exists_adj.mp nonemptyEdges
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have hne : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hpos fit)
  exact avoid (embed_three F X R A colors left hne fit rich)

end E713Triples

end

section

open SimpleGraph Finset Filter Asymptotics Real
open scoped Classical

namespace E713FiveThirds

lemma rpow_five_thirds_cube (n : ℕ) (hn : 0 < (n : ℝ)) :
    ((n : ℝ) ^ (5 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ 5 := by
  rw [← Real.rpow_natCast ((n : ℝ) ^ (5 / 3 : ℝ)) 3, ← Real.rpow_mul hn.le]
  norm_num

theorem k33_lower {V : Type*} (F : SimpleGraph V)
    (sub : completeBipartiteGraph (Fin 3) (Fin 3) ⊑ F) :
    (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) =O[atTop] (fun n : ℕ => (extremalNumber n F : ℝ)) := by
  apply isBigO_iff.mpr
  refine ⟨128, ?_⟩
  filter_upwards [eventually_ge_atTop (1000 : ℕ)] with n hn
  have pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmono : extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) ≤ extremalNumber n F :=
    E713Exponents.mono_ex sub n
  have hnat : n ^ 5 ≤ 128 ^ 3 * (extremalNumber n F) ^ 3 :=
    (E713Brown.k33_lower_uniform n hn).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmono 3))
  have hreal : (n : ℝ) ^ 5 ≤ (128 * (extremalNumber n F : ℝ)) ^ 3 := by
    rw [mul_pow]
    exact_mod_cast hnat
  rw [← rpow_five_thirds_cube n pos] at hreal
  have hle : (n : ℝ) ^ (5 / 3 : ℝ) ≤ 128 * (extremalNumber n F : ℝ) :=
    le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity) hreal
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg pos.le _),
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hle

theorem degree_three_upper {V : Type*} [Fintype V] [DecidableEq V] (F : SimpleGraph V)
    (R : Finset V) (colors : ∀ u v, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (left : ∀ v ∉ R, F.degree v ≤ 3) (nb : F ≠ ⊥) :
    (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) := by
  let C : ℝ := ((Fintype.card V : ℝ) ^ 3 + (Fintype.card V : ℝ)) + 1
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 3 + (Fintype.card V : ℝ) := by positivity
    linarith
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnat := E713Triples.degree_three_bound F R colors left n nb
  have hreal : (2 * (extremalNumber n F : ℝ)) ^ 3 ≤
      (n : ℝ) ^ 5 * ((Fintype.card V : ℝ) ^ 3 + (Fintype.card V : ℝ)) := by
    exact_mod_cast hnat
  have hCcube : (Fintype.card V : ℝ) ^ 3 + (Fintype.card V : ℝ) ≤ C ^ 3 := by
    have hsq : C ≤ C ^ 2 := by nlinarith
    have h1 : C ≤ C ^ 3 := by nlinarith
    dsimp [C] at h1 ⊢
    linarith
  have hcube : (extremalNumber n F : ℝ) ^ 3 ≤ (C * (n : ℝ) ^ (5 / 3 : ℝ)) ^ 3 := by
    rw [mul_pow, rpow_five_thirds_cube n pos]
    have h2 : (extremalNumber n F : ℝ) ^ 3 ≤ (2 * (extremalNumber n F : ℝ)) ^ 3 := by
      rw [mul_pow]
      have : (0 : ℝ) ≤ (extremalNumber n F : ℝ) ^ 3 := by positivity
      linarith
    have h3 : (n : ℝ) ^ 5 * ((Fintype.card V : ℝ) ^ 3 + (Fintype.card V : ℝ)) ≤
        C ^ 3 * (n : ℝ) ^ 5 := by
      have hn5 : (0 : ℝ) ≤ (n : ℝ) ^ 5 := by positivity
      nlinarith
    linarith
  have hle : (extremalNumber n F : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) :=
    le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity) hcube
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg pos.le _)]
  exact hle

/-- Matching `Θ(n^(5/3))` bound whenever `K_{3,3} ⊑ F` and one side has max degree at most `3`. -/
theorem k33_degree_three_theta {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R : Finset V)
    (cube : completeBipartiteGraph (Fin 3) (Fin 3) ⊑ F)
    (colors : ∀ u v, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (left : ∀ v ∉ R, F.degree v ≤ 3) :
    (fun n : ℕ => (extremalNumber n F : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) := by
  have nonemptyEdges : F ≠ ⊥ := by
    rintro rfl
    obtain ⟨copy⟩ := cube
    exact copy.toHom.map_rel' (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inl 0) (Sum.inr 0) from Or.inl ⟨rfl, rfl⟩)
  exact ⟨degree_three_upper F R colors left nonemptyEdges, k33_lower F cube⟩

end E713FiveThirds

end

open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology

namespace OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1_H2_R1

/-- Below exponent `5/3` (in `(3/2, 5/3)`) the forbidden graph must be `K_{3,3}`-free. -/
def H1 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.Connected → G.IsBipartite →
    (∀ v, 2 ≤ G.degree v) →
    (∀ R : Finset (Fin q), (∀ u v, G.Adj u v → (u ∈ R ↔ v ∉ R)) →
      ∃ v ∉ R, 3 ≤ G.degree v) →
    (completeBipartiteGraph (Fin 3) (Fin 3)).Free G →
    ∀ α : ℝ, α ∈ Set.Ioo (3 / 2 : ℝ) (5 / 3 : ℝ) →
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

/-- Above exponent `5/3` (in `(5/3, 2)`) both sides of any proper bipartition must contain
a vertex of degree at least `4`. -/
def H2 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.Connected → G.IsBipartite →
    (∀ v, 2 ≤ G.degree v) →
    (∀ R : Finset (Fin q), (∀ u v, G.Adj u v → (u ∈ R ↔ v ∉ R)) →
      ∃ v ∉ R, 4 ≤ G.degree v) →
    ∀ α : ℝ, α ∈ Set.Ioo (5 / 3 : ℝ) 2 →
      (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

theorem main : H1 → H2 → OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1.H2 := by
  intro small large q G conn bip minDeg deg3 α range big sharp
  rcases lt_trichotomy α (5 / 3 : ℝ) with lt | eq | gt
  · apply small q G conn bip minDeg deg3 _ α ⟨range.1, lt⟩ big sharp
    intro sub
    have impossible :=
      ((E713FiveThirds.k33_lower G sub).trans big).trans_isLittleO (E713Exponents.smaller lt)
    have nonzero : ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ (5 / 3 : ℝ) ≠ 0 :=
      ((eventually_gt_atTop (0 : ℕ)).mono fun n hn =>
        (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).ne').frequently
    exact isLittleO_irrefl nonzero impossible
  · exact ⟨(5 / 3 : ℚ), by push_cast; linarith⟩
  · apply large q G conn bip minDeg _ α ⟨gt, range.2⟩ big sharp
    intro R colors
    by_contra! thin
    have left (v) (out : v ∉ R) : G.degree v ≤ 3 := by have := thin v out; omega
    have nb : G ≠ ⊥ := by
      obtain ⟨v⟩ := conn.nonempty
      rintro rfl
      have h := minDeg v
      simp at h
    exact sharp ((E713FiveThirds.degree_three_upper G R colors left nb).trans_isLittleO
      (E713Exponents.smaller gt))

end OMA.R_Erdos713_erdos_713_parts_ii_R1_H2_R1_H2_R1_H2_R1
