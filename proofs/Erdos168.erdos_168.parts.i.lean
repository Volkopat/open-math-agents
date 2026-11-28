import FormalConjectures.ErdosProblems.«168»
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
The Graham–Spencer–Witsenhausen series for the nonternary density.
Each coefficient is obtained by a finite search on the smooth numbers alone.
-/
open scoped BigOperators Topology

namespace OMA
open Finset Filter

def smoothVal (p : ℕ × ℕ) : ℕ := 2 ^ p.1 * 3 ^ p.2

theorem smooth_pos (p : ℕ × ℕ) : 0 < smoothVal p := by unfold smoothVal; positivity

theorem smooth_exponents (p : ℕ × ℕ) : p.1 < smoothVal p ∧ p.2 < smoothVal p := by
  unfold smoothVal
  exact ⟨(Nat.lt_pow_self (by decide : 1 < 2)).trans_le (Nat.le_mul_of_pos_right _ (by positivity)),
    (Nat.lt_pow_self (by decide : 1 < 3)).trans_le (Nat.le_mul_of_pos_left _ (by positivity))⟩

def smoothUpTo (n : ℕ) : Finset ℕ :=
  ((range n ×ˢ range n).image smoothVal).filter (· ≤ n)

theorem mem_smooth {n d : ℕ} : d ∈ smoothUpTo n ↔ d ≤ n ∧ ∃ p, smoothVal p = d := by
  simp only [smoothUpTo, mem_filter, mem_image, mem_product, mem_range]
  constructor
  · rintro ⟨⟨p, _, rfl⟩, h⟩
    exact ⟨h, p, rfl⟩
  · rintro ⟨h, p, rfl⟩
    exact ⟨⟨p, ⟨(smooth_exponents p).1.trans_le h, (smooth_exponents p).2.trans_le h⟩, rfl⟩, h⟩

theorem smooth_inj : Function.Injective smoothVal := by
  intro p q h
  have hf (r : ℕ × ℕ) : (smoothVal r).factorization = Finsupp.single 2 r.1 + Finsupp.single 3 r.2 := by
    unfold smoothVal
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]
  have he := congrArg Nat.factorization h
  rw [hf, hf] at he
  exact Prod.ext (by simpa using congrArg (fun f : ℕ →₀ ℕ => f 2) he)
    (by simpa using congrArg (fun f : ℕ →₀ ℕ => f 3) he)

def profile (n : ℕ) : ℕ :=
  ((Icc 1 n).filter fun k => ∃ s ∈ (smoothUpTo n).powerset,
    (∀ x ∈ s, 2 * x ∉ s ∨ 3 * x ∉ s) ∧ k ≤ s.card).card

def gain (d : ℕ) : ℕ := profile d - profile (d - 1)

theorem nt_mono {s t : Finset ℕ} (hst : s ⊆ t) (ht : Erdos168.NonTernary t) : Erdos168.NonTernary s := by
  intro x
  rcases ht x with h | h | h
  · exact Or.inl (fun hx => h (hst hx))
  · exact Or.inr (Or.inl (fun hx => h (hst hx)))
  · exact Or.inr (Or.inr (fun hx => h (hst hx)))

theorem profile_spec (n : ℕ) :
    (∃ s ⊆ smoothUpTo n, Erdos168.NonTernary s ∧ s.card = profile n) ∧
    (∀ s ⊆ smoothUpTo n, Erdos168.NonTernary s → s.card ≤ profile n) := by
  classical
  let U := (smoothUpTo n).powerset.filter Erdos168.NonTernary
  obtain ⟨s, hs, he⟩ := Finset.exists_mem_eq_sup U (show U.Nonempty from
    ⟨∅, by simp [U, Erdos168.NonTernary]⟩) Finset.card
  have hupper (v : Finset ℕ) (hv : v ⊆ smoothUpTo n) (hnt : Erdos168.NonTernary v) :
      v.card ≤ s.card := by
    rw [← he]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hv, hnt⟩)
  have hs' := Finset.mem_filter.mp hs
  have hsU := Finset.mem_powerset.mp hs'.1
  have hsn : s.card ≤ n := by
    have hh : s ⊆ Icc 1 n := by
      intro d hd
      obtain ⟨hle, p, rfl⟩ := mem_smooth.mp (hsU hd)
      exact mem_Icc.mpr ⟨smooth_pos p, hle⟩
    simpa using card_le_card hh
  have hc : profile n = s.card := by
    unfold profile
    suffices hh : (Icc 1 n).filter (fun k => ∃ v ∈ (smoothUpTo n).powerset,
        (∀ x ∈ v, 2 * x ∉ v ∨ 3 * x ∉ v) ∧ k ≤ v.card) = Icc 1 s.card by
      rw [hh]
      simp
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_powerset]
    refine ⟨?_, fun ⟨hk, hks⟩ => ⟨⟨hk, hks.trans hsn⟩, s, hsU, ?_, hks⟩⟩
    · rintro ⟨⟨hk, _⟩, v, hv, hnt, hc⟩
      refine ⟨hk, hc.trans (hupper v hv ?_)⟩
      intro x
      by_cases hx : x ∈ v
      · exact Or.inr (hnt x hx)
      · exact Or.inl hx
    · intro x hx
      exact (hs'.2 x).resolve_left (fun h => h hx)
  exact ⟨⟨s, hsU, hs'.2, hc.symm⟩, fun v hv ht => hc ▸ hupper v hv ht⟩

theorem profile_mono : Monotone profile := by
  intro a b hab
  obtain ⟨s, hs, ht, he⟩ := (profile_spec a).1
  rw [← he]
  apply (profile_spec b).2 s _ ht
  intro d hd
  obtain ⟨hle, h⟩ := mem_smooth.mp (hs hd)
  exact mem_smooth.mpr ⟨hle.trans hab, h⟩

theorem gain_le (d : ℕ) : gain d ≤ 1 := by
  obtain ⟨s, hs, ht, he⟩ := (profile_spec d).1
  have hsub : s.erase d ⊆ smoothUpTo (d - 1) := by
    intro x hx
    obtain ⟨hne, hxs⟩ := Finset.mem_erase.mp hx
    obtain ⟨hle, p, rfl⟩ := mem_smooth.mp (hs hxs)
    exact mem_smooth.mpr ⟨by omega, p, rfl⟩
  have hb := (profile_spec (d - 1)).2 _ hsub (nt_mono (erase_subset _ _) ht)
  have hcard : s.card ≤ (s.erase d).card + 1 := by
    by_cases hd : d ∈ s
    · exact (Finset.card_erase_add_one hd).ge
    · simp [Finset.erase_eq_of_notMem hd]
  unfold gain
  omega

theorem gain_zero {d : ℕ} (h : d ∉ Set.range smoothVal) : gain d = 0 := by
  obtain ⟨s, hs, ht, hc⟩ := (profile_spec d).1
  have hle := (profile_spec (d - 1)).2 s (by
    intro x hx
    obtain ⟨hle, hp⟩ := mem_smooth.mp (hs hx)
    have hn : x ≠ d := fun he => h (he ▸ hp)
    exact mem_smooth.mpr ⟨by omega, hp⟩) ht
  unfold gain
  omega

lemma coprime_smooth {c : ℕ} (hc : c.Coprime 6) (p : ℕ × ℕ) : c.Coprime (smoothVal p) := by
  apply Nat.coprime_mul_iff_right.mpr
  exact ⟨(hc.of_dvd_right (by decide : 2 ∣ 6)).pow_right _,
    (hc.of_dvd_right (by decide : 3 ∣ 6)).pow_right _⟩

lemma core_unique {c c' : ℕ} {p q : ℕ × ℕ} (hc : c.Coprime 6) (hc' : c'.Coprime 6)
    (h : c * smoothVal p = c' * smoothVal q) : c = c' := by
  exact Nat.dvd_antisymm
    ((coprime_smooth hc q).dvd_of_dvd_mul_right (h ▸ dvd_mul_right c (smoothVal p)))
    ((coprime_smooth hc' p).dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right c' (smoothVal q)))

lemma coprime_six (c : ℕ) : c.Coprime 6 ↔ ¬ 2 ∣ c ∧ ¬ 3 ∣ c := by
  have h₂ : c.Coprime 2 ↔ ¬ 2 ∣ c := Nat.coprime_comm.trans Nat.prime_two.coprime_iff_not_dvd
  have h₃ : c.Coprime 3 ↔ ¬ 3 ∣ c := Nat.coprime_comm.trans Nat.prime_three.coprime_iff_not_dvd
  change c.Coprime (2 * 3) ↔ _
  rw [Nat.coprime_mul_iff_right, h₂, h₃]

lemma smooth_double (p : ℕ × ℕ) : smoothVal (p.1 + 1, p.2) = 2 * smoothVal p := by
  simp [smoothVal, pow_succ]; ring

lemma smooth_triple (p : ℕ × ℕ) : smoothVal (p.1, p.2 + 1) = 3 * smoothVal p := by
  simp [smoothVal, pow_succ]; ring

lemma core_exists (n : ℕ) (hn : 0 < n) : ∃ (c : ℕ) (p : ℕ × ℕ), c.Coprime 6 ∧ n = c * smoothVal p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h₂ : 2 ∣ n
    · obtain ⟨m, hm⟩ := h₂
      obtain ⟨c, p, hc, he⟩ := ih m (by omega) (by omega)
      exact ⟨c, (p.1 + 1, p.2), hc, by rw [hm, he, smooth_double]; ring⟩
    by_cases h₃ : 3 ∣ n
    · obtain ⟨m, hm⟩ := h₃
      obtain ⟨c, p, hc, he⟩ := ih m (by omega) (by omega)
      exact ⟨c, (p.1, p.2 + 1), hc, by rw [hm, he, smooth_triple]; ring⟩
    exact ⟨n, (0, 0), (coprime_six n).mpr ⟨h₂, h₃⟩, by simp [smoothVal]⟩

def cores (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun c => c.Coprime 6)

lemma mem_cores {N c : ℕ} : c ∈ cores N ↔ (0 < c ∧ c ≤ N) ∧ c.Coprime 6 := by
  simp [cores, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

lemma core_bound {c d N : ℕ} (hc : 0 < c) : d ≤ N / c ↔ c * d ≤ N := by
  rw [Nat.le_div_iff_mul_le hc, Nat.mul_comm]

def assemble (N : ℕ) (s : ℕ → Finset ℕ) : Finset ℕ := (cores N).biUnion fun c => (s c).image (c * ·)

lemma mem_assemble {N : ℕ} {s : ℕ → Finset ℕ} {n : ℕ} :
    n ∈ assemble N s ↔ ∃ c ∈ cores N, ∃ d ∈ s c, c * d = n := by simp [assemble]

lemma card_assemble {N : ℕ} {s : ℕ → Finset ℕ} (hs : ∀ c, s c ⊆ smoothUpTo (N / c)) :
    (assemble N s).card = ∑ c ∈ cores N, (s c).card := by
  unfold assemble
  rw [Finset.card_biUnion]
  · apply sum_congr rfl
    intro c hc
    exact card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left (mem_cores.mp hc).1.1 h)
  · intro c hc c' hc' hne
    apply disjoint_left.mpr
    intro n hn hn'
    obtain ⟨d, hd, he⟩ := mem_image.mp hn
    obtain ⟨d', hd', he'⟩ := mem_image.mp hn'
    obtain ⟨_, p, rfl⟩ := mem_smooth.mp (hs c hd)
    obtain ⟨_, q, rfl⟩ := mem_smooth.mp (hs c' hd')
    exact hne (core_unique (mem_cores.mp hc).2 (mem_cores.mp hc').2 (he.trans he'.symm))

lemma assemble_good {N : ℕ} {s : ℕ → Finset ℕ} (hs : ∀ c, s c ⊆ smoothUpTo (N / c))
    (ht : ∀ c, Erdos168.NonTernary (s c)) : assemble N s ∈ Erdos168.IntervalNonTernarySets N := by
  rw [Erdos168.mem_IntervalNonTernarySets_iff]
  constructor
  · intro n
    by_contra! h
    obtain ⟨c, hc, d, hd, he⟩ := mem_assemble.mp h.1
    obtain ⟨b, hb, e, hE, he₂⟩ := mem_assemble.mp h.2.1
    obtain ⟨a, ha, f, hf, he₃⟩ := mem_assemble.mp h.2.2
    obtain ⟨_, p, rfl⟩ := mem_smooth.mp (hs c hd)
    obtain ⟨_, q, rfl⟩ := mem_smooth.mp (hs b hE)
    obtain ⟨_, r, rfl⟩ := mem_smooth.mp (hs a hf)
    have eq₂ : c * (2 * smoothVal p) = b * smoothVal q := by rw [he₂, ← he]; ring
    have eq₃ : c * (3 * smoothVal p) = a * smoothVal r := by rw [he₃, ← he]; ring
    have e₂ : c * smoothVal (p.1 + 1, p.2) = b * smoothVal q := by rw [smooth_double]; exact eq₂
    have e₃ : c * smoothVal (p.1, p.2 + 1) = a * smoothVal r := by rw [smooth_triple]; exact eq₃
    have hcb := core_unique (mem_cores.mp hc).2 (mem_cores.mp hb).2 e₂
    have hca := core_unique (mem_cores.mp hc).2 (mem_cores.mp ha).2 e₃
    subst b
    subst a
    have h₂ := Nat.eq_of_mul_eq_mul_left (mem_cores.mp hc).1.1 eq₂
    have h₃ := Nat.eq_of_mul_eq_mul_left (mem_cores.mp hc).1.1 eq₃
    rcases ht c (smoothVal p) with h | h | h
    · exact h hd
    · exact h (h₂ ▸ hE)
    · exact h (h₃ ▸ hf)
  · intro n hn
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_assemble.mp hn
    obtain ⟨hle, p, rfl⟩ := mem_smooth.mp (hs c hd)
    have hp := (mem_cores.mp hc).1.1
    exact mem_Icc.mpr ⟨Nat.mul_pos hp (smooth_pos p), (core_bound hp).mp hle⟩

lemma F_split (N : ℕ) : Erdos168.F N = ∑ c ∈ cores N, profile (N / c) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    obtain ⟨hSnt, hSI⟩ := (Erdos168.mem_IntervalNonTernarySets_iff N S).mp hS
    let s (c : ℕ) := (smoothUpTo (N / c)).filter (fun d => c * d ∈ S)
    have hsub (c : ℕ) : s c ⊆ smoothUpTo (N / c) := filter_subset _ _
    have hnt (c : ℕ) : Erdos168.NonTernary (s c) := by
      intro d
      by_contra! h
      have e₂ : c * (2 * d) = 2 * (c * d) := by ring
      have e₃ : c * (3 * d) = 3 * (c * d) := by ring
      rcases hSnt (c * d) with hh | hh | hh
      · exact hh (mem_filter.mp h.1).2
      · exact hh (e₂ ▸ (mem_filter.mp h.2.1).2)
      · exact hh (e₃ ▸ (mem_filter.mp h.2.2).2)
    have hcover : S ⊆ assemble N s := by
      intro n hn
      obtain ⟨hpos, hle⟩ := mem_Icc.mp (hSI hn)
      obtain ⟨c, p, hc, rfl⟩ := core_exists n hpos
      have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
      have hcN := (Nat.le_mul_of_pos_right c (smooth_pos p)).trans hle
      refine mem_assemble.mpr ⟨c, mem_cores.mpr ⟨⟨hcpos, hcN⟩, hc⟩, smoothVal p, ?_, rfl⟩
      exact mem_filter.mpr ⟨mem_smooth.mpr ⟨(core_bound hcpos).mpr hle, p, rfl⟩, hn⟩
    calc
      S.card ≤ (assemble N s).card := card_le_card hcover
      _ = ∑ c ∈ cores N, (s c).card := card_assemble hsub
      _ ≤ _ := sum_le_sum (fun c _ => (profile_spec (N / c)).2 (s c) (hsub c) (hnt c))
  · have hex (c : ℕ) := (profile_spec (N / c)).1
    choose s hsub hnt hcard using hex
    rw [← show (assemble N s).card = ∑ c ∈ cores N, profile (N / c) by
      rw [card_assemble hsub]; simp only [hcard]]
    exact le_sup (assemble_good hsub hnt)

lemma profile_sum (m : ℕ) : profile m = ∑ d ∈ Icc 1 m, gain d := by
  induction m with
  | zero => simp [profile]
  | succ m ih =>
    have he : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
      ext d
      simp only [mem_Icc, mem_insert]
      omega
    rw [he, sum_insert (by simp only [mem_Icc]; omega), ← ih]
    rw [gain, show m + 1 - 1 = m by omega, Nat.sub_add_cancel (profile_mono (Nat.le_succ m))]

lemma core_filter (N d : ℕ) (hd : 0 < d) :
    (cores N).filter (fun c => d ≤ N / c) = cores (N / d) := by
  ext c
  simp only [mem_filter, mem_cores]
  constructor
  · rintro ⟨⟨⟨hc, _⟩, hcop⟩, h⟩
    exact ⟨⟨hc, (core_bound hd).mpr (by simpa [mul_comm] using (core_bound hc).mp h)⟩, hcop⟩
  · rintro ⟨⟨hc, h⟩, hcop⟩
    exact ⟨⟨⟨hc, h.trans (Nat.div_le_self _ _)⟩, hcop⟩,
      (core_bound hc).mpr (by simpa [mul_comm] using (core_bound hd).mp h)⟩

lemma F_sum (N : ℕ) : Erdos168.F N = ∑ d ∈ Icc 1 N, gain d * (cores (N / d)).card := by
  rw [F_split]
  calc
    _ = ∑ c ∈ cores N, ∑ d ∈ Icc 1 N, if d ≤ N / c then gain d else 0 := by
      apply sum_congr rfl
      intro c _
      rw [profile_sum, ← sum_filter]
      congr 1
      ext d
      simp only [mem_filter, mem_Icc]
      have := Nat.div_le_self N c
      omega
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter, core_filter N d (mem_Icc.mp hd).1]
      simp [mul_comm]

lemma coprime_residues (c : ℕ) : c.Coprime 6 ↔ c % 6 = 1 ∨ c % 6 = 5 := by
  rw [coprime_six]
  simp only [Nat.dvd_iff_mod_eq_zero]
  rw [← Nat.mod_mod_of_dvd c (by decide : 2 ∣ 6),
    ← Nat.mod_mod_of_dvd c (by decide : 3 ∣ 6)]
  omega

lemma cores_count (M : ℕ) : (cores M).card = (M + 5) / 6 + (M + 1) / 6 := by
  let R (r : ℕ) := (Icc 1 M).filter fun c => c % 6 = r
  have hR (r : ℕ) (hr : 0 < r) (hr' : r < 6) : (R r).card = (M + (6 - r)) / 6 := by
    have e : R r = (range ((M + (6 - r)) / 6)).image (fun i => 6 * i + r) := by
      ext c
      simp only [R, mem_filter, mem_Icc, mem_image, mem_range]
      constructor
      · rintro ⟨⟨_, hc⟩, hcr⟩
        exact ⟨c / 6, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [e, card_image_of_injective _ (fun _ _ h => by omega), card_range]
  have h : cores M = R 1 ∪ R 5 := by
    ext c
    simp only [cores, R, mem_filter, mem_union, coprime_residues]
    tauto
  have hd : Disjoint (R 1) (R 5) := disjoint_left.mpr (by simp only [R, mem_filter]; omega)
  rw [h, card_union_of_disjoint hd, hR 1 (by decide) (by decide), hR 5 (by decide) (by decide)]

lemma cores_density (t : ℕ) (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((cores (N / t)).card : ℝ) / N) atTop (𝓝 (1 / (3 * (t : ℝ)))) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have h₃ : 0 < (3 : ℝ) * t := by positivity
  have herror (N : ℕ) : |((cores (N / t)).card : ℝ) - (N : ℝ) / (3 * t)| ≤ 2 := by
    let q := N / (6 * t)
    have hq : q = (N / t) / 6 := by simp [q, Nat.div_div_eq_div_mul, mul_comm]
    have hlo : 2 * q ≤ (cores (N / t)).card := by rw [hq, cores_count]; omega
    have hhi : (cores (N / t)).card ≤ 2 * q + 2 := by rw [hq, cores_count]; omega
    have hlo' : (2 : ℝ) * q ≤ (cores (N / t)).card := by exact_mod_cast hlo
    have hhi' : ((cores (N / t)).card : ℝ) ≤ 2 * q + 2 := by exact_mod_cast hhi
    have hr : ((N % (6 * t) : ℕ) : ℝ) < 6 * (t : ℝ) := by exact_mod_cast Nat.mod_lt N (by positivity : 0 < 6 * t)
    have hr' : (0 : ℝ) ≤ ((N % (6 * t) : ℕ) : ℝ) := by positivity
    have he : ((N % (6 * t) : ℕ) : ℝ) + 6 * (t : ℝ) * q = N := by
      exact_mod_cast Nat.mod_add_div N (6 * t)
    have hq' : (2 : ℝ) * q ≤ N / (3 * t) ∧ (N : ℝ) / (3 * t) ≤ 2 * (q : ℝ) + 2 := by
      constructor
      · rw [le_div_iff₀ h₃]; linarith
      · rw [div_le_iff₀ h₃]; linarith
    exact abs_le.mpr ⟨by linarith [hq'.2], by linarith [hq'.1]⟩
  have hinv : Tendsto (fun N : ℕ => (2 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hinv ε hε
  refine ⟨max M 1, fun N hN => ?_⟩
  have hp : (0 : ℝ) < N := by exact_mod_cast ((le_max_right M 1).trans hN)
  rw [Real.dist_eq, show ((cores (N / t)).card : ℝ) / N - 1 / (3 * (t : ℝ)) =
    (((cores (N / t)).card : ℝ) - (N : ℝ) / (3 * t)) / N by field_simp, abs_div, abs_of_pos hp]
  apply (div_le_div_of_nonneg_right (herror N) hp.le).trans_lt
  simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) / N)] using hM N ((le_max_left _ _).trans hN)

lemma summable_smooth : Summable (fun p : ℕ × ℕ => 1 / (smoothVal p : ℝ)) := by
  have h₂ : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := summable_geometric_of_norm_lt_one (by norm_num)
  have h₃ : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ n) := summable_geometric_of_norm_lt_one (by norm_num)
  have hEq (p : ℕ × ℕ) : 1 / (smoothVal p : ℝ) = (1 / 2 : ℝ) ^ p.1 * (1 / 3 : ℝ) ^ p.2 := by
    simp [smoothVal, one_div, inv_pow, mul_comm]
  have hn₂ : 0 ≤ (fun n : ℕ => (1 / 2 : ℝ) ^ n) := fun n => by positivity
  have hn₃ : 0 ≤ (fun n : ℕ => (1 / 3 : ℝ) ^ n) := fun n => by positivity
  simpa only [hEq] using h₂.mul_of_nonneg h₃ hn₂ hn₃

noncomputable def term (N d : ℕ) : ℝ := (gain d : ℝ) * ((cores (N / d)).card : ℝ) / N

lemma term_limit (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N => term N d) atTop (𝓝 ((gain d : ℝ) / (3 * d))) := by
  simpa only [term, ← mul_div_assoc, mul_one] using (cores_density d hd).const_mul (gain d : ℝ)

lemma term_bound (N d : ℕ) : ‖term N d‖ ≤ 1 / (d : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold term; positivity), term]
  have hcard : (cores (N / d)).card ≤ N / d := by
    simpa [cores] using (card_le_card (filter_subset (fun c : ℕ => c.Coprime 6) (Icc 1 (N / d))))
  have hc : ((cores (N / d)).card : ℝ) ≤ (N : ℝ) / d :=
    (by exact_mod_cast hcard : ((cores (N / d)).card : ℝ) ≤ ((N / d : ℕ) : ℝ)).trans (Nat.cast_div_le)
  have hg' : (gain d : ℝ) ≤ 1 := by exact_mod_cast gain_le d
  calc
    _ ≤ ((cores (N / d)).card : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa using mul_le_mul_of_nonneg_right hg' (Nat.cast_nonneg (α := ℝ) (cores (N / d)).card)
    _ ≤ (N / (d : ℝ)) / N := div_le_div_of_nonneg_right hc (by positivity)
    _ ≤ 1 / (d : ℝ) := by
      by_cases hN : N = 0
      · subst N; simp
      · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
        rw [div_right_comm, div_self hN']

lemma limit_series :
    Tendsto (fun N => ∑' p : ℕ × ℕ, term N (smoothVal p)) atTop
      (𝓝 (∑' p : ℕ × ℕ, (gain (smoothVal p) : ℝ) / (3 * smoothVal p))) := by
  exact tendsto_tsum_of_dominated_convergence summable_smooth
    (fun p => term_limit (smoothVal p) (smooth_pos p))
    (Filter.Eventually.of_forall fun N p => term_bound N (smoothVal p))

lemma term_series (N : ℕ) : (Erdos168.F N : ℝ) / N = ∑' p : ℕ × ℕ, term N (smoothVal p) := by
  have hr : Function.support (term N) ⊆ Set.range smoothVal := by
    intro d hd
    by_contra he
    exact hd (by simp [term, gain_zero he])
  have hfinite (d : ℕ) (hd : d ∉ Icc 1 N) : term N d = 0 := by
    by_cases h0 : d = 0
    · subst d; simp [term, gain]
    have hN : N < d := by
      simp only [mem_Icc] at hd
      omega
    simp [term, Nat.div_eq_of_lt hN, cores]
  rw [smooth_inj.tsum_eq hr, tsum_eq_sum hfinite, F_sum]
  push_cast
  rw [Finset.sum_div]; rfl

end OMA

noncomputable def OMA.answer : ℝ := ∑' p : ℕ × ℕ, (OMA.gain (OMA.smoothVal p) : ℝ) / (3 * OMA.smoothVal p)

theorem OMA.solution : Erdos168.erdos_168.parts.i.answer = OMA.answer → type_of% @Erdos168.erdos_168.parts.i := by
  intro h
  rw [h]
  simpa only [OMA.answer, ← OMA.term_series] using OMA.limit_series
