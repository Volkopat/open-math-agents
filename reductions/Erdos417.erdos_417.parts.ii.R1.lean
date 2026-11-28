import FormalConjectures.ErdosProblems.«417»

-- Credit: @Pixelstorm44
/-!
Split the excess over the values attained by input x according to whether
a positive preimage has appeared by input 2x. Distinct values are counted
once regardless of multiplicity. The full range includes totient zero, so
the exceptional set in H2 also includes zero for nonnegative x.
-/
namespace OMA.R_Erdos417_erdos_417_parts_ii_R1

open Nat Set Filter
open scoped Topology

/-- The relative count of newly seen values up to x stabilizes in the fixed window. -/
def H1 : Prop :=
  let D (x : ℝ) := totient '' {m : ℕ | 1 ≤ m ∧ (m : ℝ) ≤ x}
  let W (x : ℝ) := {k : ℕ | (k : ℝ) ≤ x} ∩ D (2*x)
  ∃ a : ℝ, Tendsto (fun x ↦ ((W x \ D x).ncard : ℝ) / (D x).ncard) atTop (𝓝 a)

/-- Values up to x still missing at input 2x contribute a negligible proportion. -/
def H2 : Prop :=
  let D (x : ℝ) := totient '' {m : ℕ | 1 ≤ m ∧ (m : ℝ) ≤ x}
  let W (x : ℝ) := {k : ℕ | (k : ℝ) ≤ x} ∩ D (2*x)
  let V (x : ℝ) := {k : ℕ | k ∈ range totient ∧ (k : ℝ) ≤ x}
  Tendsto (fun x ↦ ((V x \ W x).ncard : ℝ) / (D x).ncard) atTop (𝓝 0)

/-- At unbounded cutoffs the upper half of the output interval alone supplies
a fixed positive proportion of new values between inputs x and 2x. -/
def H3 : Prop :=
  let D (x : ℝ) := totient '' {m : ℕ | 1 ≤ m ∧ (m : ℝ) ≤ x}
  let W (x : ℝ) := {k : ℕ | (k : ℝ) ≤ x} ∩ D (2*x)
  ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ x in atTop,
    δ ≤ (((W x \ D x) ∩ {k : ℕ | x/2 < (k : ℝ)}).ncard : ℝ) / (D x).ncard

theorem main : H1 → H2 → H3 → type_of% @Erdos417.erdos_417.parts.ii := by
  let D (x : ℝ) := totient '' {m : ℕ | 1 ≤ m ∧ (m : ℝ) ≤ x}
  let W (x : ℝ) := {k : ℕ | (k : ℝ) ≤ x} ∩ D (2*x)
  let V (x : ℝ) := {k : ℕ | k ∈ range totient ∧ (k : ℝ) ≤ x}
  intro h₁ h₂ h₃
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨δ, hδ, hfreq⟩ := h₃
  change Tendsto (fun x ↦ ((W x \ D x).ncard : ℝ) / (D x).ncard) atTop (𝓝 a) at ha
  change Tendsto (fun x ↦ ((V x \ W x).ncard : ℝ) / (D x).ncard) atTop (𝓝 0) at h₂
  have hfin (x : ℝ) : (V x).Finite :=
    (finite_Iic ⌊x⌋₊).subset fun _ hk ↦ Nat.le_floor hk.2
  have hWV (x : ℝ) : W x ⊆ V x := by
    rintro k ⟨hk, m, _, rfl⟩
    exact ⟨⟨m, rfl⟩, hk⟩
  have hDW (x : ℝ) (hx : 1 ≤ x) : D x ⊆ W x := by
    rintro k ⟨m, ⟨hm, hmx⟩, rfl⟩
    exact ⟨(Nat.cast_le.mpr (totient_le m)).trans hmx,
      ⟨m, ⟨hm, by change (m : ℝ) ≤ 2*x; linarith⟩, rfl⟩⟩
  have hδa : δ ≤ a := by
    apply ge_of_tendsto_of_frequently ha
    apply hfreq.mono
    intro x hx
    have hw := (hfin x).subset (hWV x)
    exact hx.trans (div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (ncard_le_ncard inter_subset_left (hw.sdiff (t := D x)))) (by positivity))
  refine ⟨ENNReal.ofReal (1+a), ENNReal.one_lt_ofReal.mpr (by linarith), ?_⟩
  have hlim := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (1 : ℝ))).add ha |>.add h₂)
  rw [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hw := (hfin x).subset (hWV x)
  have hd := hw.subset (hDW x hx)
  have hpos : 0 < ((D x).ncard : ℝ) := by
    exact_mod_cast (ncard_pos hd).mpr ⟨totient 1, 1, ⟨le_rfl, by simpa using hx⟩, rfl⟩
  have htotal : ((V x).ncard : ℝ) =
      (D x).ncard + (W x \ D x).ncard + (V x \ W x).ncard := by
    have h₁ := ncard_sdiff_add_ncard_of_subset (hDW x hx) hw
    have h₂ := ncard_sdiff_add_ncard_of_subset (hWV x) (hfin x)
    exact_mod_cast (show (V x).ncard = _ by omega)
  change ENNReal.ofReal (1 + ((W x \ D x).ncard : ℝ) / (D x).ncard +
    ((V x \ W x).ncard : ℝ) / (D x).ncard) = ((V x).ncard : ENNReal) / (D x).ncard
  rw [← ENNReal.ofReal_natCast (V x).ncard, ← ENNReal.ofReal_natCast (D x).ncard,
    ← ENNReal.ofReal_div_of_pos hpos]
  congr 1
  rw [htotal, add_div, add_div, div_self hpos.ne']

end OMA.R_Erdos417_erdos_417_parts_ii_R1
