import OMAReductions.R_Erdos564_erdos_564_R2

-- Reduction Erdos564.erdos_564.R2.H2.R1 of Erdos564.erdos_564.R2.H2
-- Credit: @sanchan
-- Splits the 2-to-4 color linear comparison for 3-uniform hypergraphs (resting on the
-- already-solved 4-color stepping-up tower R2.H1) into two lossless single-color jumps:
-- H1 (2 colors -> 3 colors at hypergraphRamsey 3 n) and H2 (3 colors -> 4 colors for
-- every 3-color forcing pair (m, k)), relaxing exact clique size to lower bounds via
-- proved clique-trimming and vertex/color monotonicity theorems.

open Filter Combinatorics

namespace OMA.R_Erdos564_erdos_564_R2_H2_R1

/-- Single-color jump from 2 to 3 colors at the 2-color threshold `hypergraphRamsey 3 n`:
every 3-coloring of the triples of `Fin (hypergraphRamsey 3 n)` has a monochromatic set
of size at least `c * n`. Lossless (implied by `Erdos564.R2.H2` by embedding `Fin 3 ↪ Fin 4`). -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, c * n ≤ k ∧
    ∀ f : Finset (Fin (hypergraphRamsey 3 n)) → Fin 3,
      ∃ S : Finset (Fin (hypergraphRamsey 3 n)), k ≤ S.card ∧
        ∃ b : Fin 3, ∀ e : Finset (Fin (hypergraphRamsey 3 n)),
          e ⊆ S → e.card = 3 → f e = b

/-- Single-color jump from 3 to 4 colors: for all sufficiently large `k`, whenever every
3-coloring of the triples of `Fin m` has a monochromatic set of size `k`, every 4-coloring
of the triples of `Fin m` has a monochromatic set of size at least `c * k`. Lossless
(implied by `Erdos564.R2.H2` since 3-color forcing implies `hypergraphRamsey 3 k ≤ m`). -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∀ m : ℕ,
    (∀ f : Finset (Fin m) → Fin 3,
      ∃ S : Finset (Fin m), S.card = k ∧
        ∃ b : Fin 3, ∀ e : Finset (Fin m), e ⊆ S → e.card = 3 → f e = b) →
    ∃ l : ℕ, c * k ≤ l ∧
      ∀ f : Finset (Fin m) → Fin 4,
        ∃ S : Finset (Fin m), l ≤ S.card ∧
          ∃ b : Fin 4, ∀ e : Finset (Fin m), e ⊆ S → e.card = 3 → f e = b

/-- Clique-size trimming: any monochromatic set of size at least `k` contains a
monochromatic subset of exact cardinality `k`. -/
theorem trim_monochromatic {m c k : ℕ} {f : Finset (Fin m) → Fin c}
    {S : Finset (Fin m)} (hcard : k ≤ S.card) {b : Fin c}
    (hmono : ∀ e : Finset (Fin m), e ⊆ S → e.card = 3 → f e = b) :
    ∃ T : Finset (Fin m), T.card = k ∧
      ∀ e : Finset (Fin m), e ⊆ T → e.card = 3 → f e = b := by
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨T, hTcard, fun e heT he3 => hmono e (heT.trans hTS) he3⟩

/-- Vertex monotonicity for 3-uniform `c`-color Ramsey forcing: if `m1 ≤ m2` and `Fin m1`
forces a monochromatic `k`-set, then so does `Fin m2`. -/
theorem ramsey3_mono {m1 m2 c k : ℕ} (hm : m1 ≤ m2)
    (h1 : ∀ f : Finset (Fin m1) → Fin c,
      ∃ S : Finset (Fin m1), S.card = k ∧
        ∃ b : Fin c, ∀ e : Finset (Fin m1), e ⊆ S → e.card = 3 → f e = b) :
    ∀ f : Finset (Fin m2) → Fin c,
      ∃ S : Finset (Fin m2), S.card = k ∧
        ∃ b : Fin c, ∀ e : Finset (Fin m2), e ⊆ S → e.card = 3 → f e = b := by
  intro f
  let ι : Fin m1 ↪ Fin m2 := Fin.castLEEmb hm
  obtain ⟨S, hScard, b, hSmono⟩ := h1 (fun e => f (e.map ι))
  refine ⟨S.map ι, by rw [Finset.card_map, hScard], b, fun e he he3 => ?_⟩
  have hsub : ∀ x ∈ e, x ∈ S.map ι := fun x hx => he hx
  let pre : Finset (Fin m1) := S.filter (fun y => ι y ∈ e)
  have hmap : pre.map ι = e := by
    ext x
    simp only [pre, Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨_, hy⟩, rfl⟩
      exact hy
    · intro hx
      rcases Finset.mem_map.mp (hsub x hx) with ⟨y, hyS, rfl⟩
      exact ⟨y, ⟨hyS, hx⟩, rfl⟩
  have hpre_sub : pre ⊆ S := Finset.filter_subset _ _
  have hpre_card : pre.card = 3 := by
    have := Finset.card_map ι (s := pre)
    rw [hmap] at this
    omega
  simpa [hmap] using hSmono pre hpre_sub hpre_card

/-- Color monotonicity for 3-uniform Ramsey forcing (`k ≥ 3`): forcing with `c2` colors
implies forcing with `c1 ≤ c2` colors. -/
theorem ramsey3_of_le_colors {m c1 c2 k : ℕ} (hc : c1 ≤ c2) (hk : 3 ≤ k)
    (h2 : ∀ f : Finset (Fin m) → Fin c2,
      ∃ S : Finset (Fin m), S.card = k ∧
        ∃ b : Fin c2, ∀ e : Finset (Fin m), e ⊆ S → e.card = 3 → f e = b) :
    ∀ f : Finset (Fin m) → Fin c1,
      ∃ S : Finset (Fin m), S.card = k ∧
        ∃ b : Fin c1, ∀ e : Finset (Fin m), e ⊆ S → e.card = 3 → f e = b := by
  intro f
  obtain ⟨S, hScard, b, hSmono⟩ := h2 (fun e => Fin.castLE hc (f e))
  obtain ⟨e0, he0S, he0card⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ S.card)
  have hb : Fin.castLE hc (f e0) = b := hSmono e0 he0S he0card
  refine ⟨S, hScard, f e0, fun e heS he3 => ?_⟩
  have hfe : Fin.castLE hc (f e) = Fin.castLE hc (f e0) := (hSmono e heS he3).trans hb.symm
  exact Fin.ext (by simpa using congrArg Fin.val hfe)

theorem main : H1 → H2 → OMA.R_Erdos564_erdos_564_R2.H2 := by
  rintro ⟨c1, hc1, h1⟩ ⟨c2, hc2, h2⟩
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 h2
  refine ⟨c2 * c1, mul_pos hc2 hc1, ?_⟩
  filter_upwards [h1, eventually_ge_atTop ⌈(k0 : ℝ) / c1⌉₊] with n hn hlarge
  obtain ⟨k, hck, hforce3⟩ := hn
  have h3 : (k0 : ℝ) / c1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hlarge)
  have hk_ge_real : (k0 : ℝ) ≤ (k : ℝ) := by
    have hmul : (k0 : ℝ) ≤ c1 * n := by
      have := (div_le_iff₀ hc1).1 h3
      linarith
    exact hmul.trans hck
  have hk_ge : k0 ≤ k := by exact_mod_cast hk_ge_real
  have hforce3_exact : ∀ f : Finset (Fin (hypergraphRamsey 3 n)) → Fin 3,
      ∃ S : Finset (Fin (hypergraphRamsey 3 n)), S.card = k ∧
        ∃ b : Fin 3, ∀ e : Finset (Fin (hypergraphRamsey 3 n)),
          e ⊆ S → e.card = 3 → f e = b := by
    intro f
    obtain ⟨S, hScard, b, hSmono⟩ := hforce3 f
    obtain ⟨T, hTcard, hTmono⟩ := trim_monochromatic hScard hSmono
    exact ⟨T, hTcard, b, hTmono⟩
  obtain ⟨l, hcl, hforce4⟩ := hk0 k hk_ge (hypergraphRamsey 3 n) hforce3_exact
  refine ⟨l, ?_, fun f => ?_⟩
  · calc (c2 * c1) * (n : ℝ) = c2 * (c1 * (n : ℝ)) := by ring
      _ ≤ c2 * (k : ℝ) := mul_le_mul_of_nonneg_left hck hc2.le
      _ ≤ (l : ℝ) := hcl
  · obtain ⟨S, hScard, b, hSmono⟩ := hforce4 f
    obtain ⟨T, hTcard, hTmono⟩ := trim_monochromatic hScard hSmono
    exact ⟨T, hTcard, b, hTmono⟩

end OMA.R_Erdos564_erdos_564_R2_H2_R1
