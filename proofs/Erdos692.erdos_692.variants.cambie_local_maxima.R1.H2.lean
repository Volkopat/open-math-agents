import OMAReductions.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1

-- Periodic density lemmas adapted from the merged Erdős 1064 proof.
open Filter Set Topology Erdos692
namespace CambieDrop
open scoped Classical
noncomputable def cnt (S : Set ℕ) (b : ℕ) : ℕ := ((Finset.range b).filter (· ∈ S)).card

lemma pd_eq (S : Set ℕ) (b : ℕ) : S.partialDensity Set.univ b = (cnt S b : ℝ) / b := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have h1 : S ∩ Iio b = ↑((Finset.range b).filter (· ∈ S)) := by
    ext n; simp [and_comm]
  rw [h1, Set.ncard_coe_finset, Nat.ncard_Iio]
  simp [cnt]

lemma hasDensity_iff (S : Set ℕ) (d : ℝ) :
    S.HasDensity d ↔ Tendsto (fun b => (cnt S b : ℝ) / b) atTop (𝓝 d) := by
  simp only [Set.HasDensity, pd_eq]

lemma cnt_succ (S : Set ℕ) (n : ℕ) :
    cnt S (n + 1) = cnt S n + (if n ∈ S then 1 else 0) := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma cnt_le (S : Set ℕ) (n : ℕ) : cnt S n ≤ n := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

def Per (Y : Set ℕ) (N : ℕ) : Prop := ∀ n, n ∈ Y ↔ n + N ∈ Y

lemma Per.mem_add_mul {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n k : ℕ) :
    n ∈ Y ↔ n + N * k ∈ Y := by
  induction k with
  | zero => simp
  | succ k ih => rw [ih, h (n + N * k)]; ring_nf

lemma Per.mem_mod {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n : ℕ) : n ∈ Y ↔ n % N ∈ Y := by
  rw [h.mem_add_mul (n % N) (n / N), Nat.mod_add_div]

lemma Per.cnt_add {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n : ℕ) :
    cnt Y (n + N) = cnt Y n + cnt Y N := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    rw [show n + 1 + N = (n + N) + 1 by ring, cnt_succ, ih, cnt_succ]
    have := h n
    by_cases hn : n ∈ Y
    · rw [if_pos hn, if_pos (this.1 hn)]; omega
    · rw [if_neg hn, if_neg (fun h' => hn (this.2 h'))]; omega

lemma Per.cnt_approx {Y : Set ℕ} {N : ℕ} (h : Per Y N) (hN : 0 < N) (n : ℕ) :
    |(cnt Y n : ℝ) - n * (cnt Y N) / N| ≤ N := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N
    · have h1 : (cnt Y n : ℝ) ≤ n := by exact_mod_cast cnt_le Y n
      have h2 : (cnt Y N : ℝ) ≤ N := by exact_mod_cast cnt_le Y N
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h3 : (n : ℝ) * cnt Y N / N ≤ n := by
        rw [div_le_iff₀ hN']; exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : (0 : ℝ) ≤ n * cnt Y N / N := by positivity
      have h5 : (n : ℝ) ≤ N := by exact_mod_cast hn.le
      rw [abs_le]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (cnt Y n)]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
      have := ih m (by omega)
      rw [h.cnt_add]
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have e : ((cnt Y m + cnt Y N : ℕ) : ℝ) - ((m + N : ℕ) : ℝ) * cnt Y N / N
          = (cnt Y m : ℝ) - m * cnt Y N / N := by
        push_cast; field_simp; ring
      rw [e]; exact this

lemma Per.hasDensity {Y : Set ℕ} {N : ℕ} (h : Per Y N) (hN : 0 < N) :
    Y.HasDensity ((cnt Y N : ℝ) / N) := by
  rw [hasDensity_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n0, hn0⟩ := exists_nat_gt ((N : ℝ) / ε)
  refine ⟨n0 + 1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (N : ℝ) / ε < n := lt_of_lt_of_le hn0 (by exact_mod_cast (show n0 ≤ n by omega))
  rw [Real.dist_eq]
  have e : (cnt Y n : ℝ) / n - cnt Y N / N = ((cnt Y n : ℝ) - n * cnt Y N / N) / n := by
    field_simp
  rw [e, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
  refine lt_of_le_of_lt (h.cnt_approx hN n) ?_
  rwa [div_lt_iff₀ hε, mul_comm] at hn'

lemma HasDensity.unique {S : Set ℕ} {a b : ℝ} (ha : S.HasDensity a) (hb : S.HasDensity b) :
    a = b := tendsto_nhds_unique ha hb

lemma factor_between {n q d : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hd : n < d) (hlt : d < 2*q) (hdv : d ∣ 2*q) : d = q := by
  obtain ⟨t, ht⟩ := hdv
  have hqt : q ∣ d*t := ht ▸ dvd_mul_left q 2
  rcases hq.dvd_mul.mp hqt with h | h
  · obtain ⟨s, hs⟩ := h
    have hs1 : s = 1 := by
      by_contra hne
      have hs2 : 2 ≤ s := by
        by_cases hz : s = 0
        · simp [hz] at hs
          omega
        · omega
      nlinarith [Nat.mul_le_mul_left q hs2]
    simpa [hs1] using hs
  · obtain ⟨u, hu⟩ := h
    have hprod : 2*q = (d*u)*q := by rw [ht, hu]; ring
    have he : 2 = d*u := Nat.eq_of_mul_eq_mul_right hq.pos hprod
    have hu1 : 1 ≤ u := by
      cases u with
      | zero => simp at he
      | succ u => omega
    nlinarith [Nat.mul_le_mul_left d hu1]

lemma periodic_set {n m L : ℕ} (hn : 0 < n)
    (hL : ∀ d, n < d → d < m → d ∣ L) : Per (exactlyOneDivisorIn n m) L := by
  intro x
  unfold exactlyOneDivisorIn
  have he : {d ∈ Set.Ioo n m | d ∣ x} = {d ∈ Set.Ioo n m | d ∣ x + L} := by
    ext d
    change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨h, hd⟩
      exact ⟨h, dvd_add hd (hL d h.1 h.2)⟩
    · rintro ⟨h, hd⟩
      exact ⟨h, (Nat.dvd_add_iff_left (hL d h.1 h.2)).mpr hd⟩
  change _ = 1 ↔ _ = 1
  rw [he]

lemma drop (δ : ℕ → ℕ → ℝ) (hδ : ∀ a b, IsDelta₁ a b (δ a b))
    (n q : ℕ) (hn : 2 ≤ n) (hq : n < q) (hp : q.Prime) :
    δ n (2*q+1) < δ n (2*q) := by
  classical
  let L := (2*q+1).factorial
  have hL : 2*q < L := lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.self_le_factorial _)
  have perd (m : ℕ) (hm : m ≤ 2*q+1) : Per (exactlyOneDivisorIn n m) L :=
    periodic_set (by omega) fun d hnd hdm => Nat.dvd_factorial (by omega) (by omega)
  have density (m : ℕ) (hm : m ≤ 2*q+1) : δ n m = (cnt (exactlyOneDivisorIn n m) L : ℝ) / L :=
    HasDensity.unique (hδ n m) ((perd m hm).hasDensity (Nat.factorial_pos _))
  rw [density _ le_rfl, density _ (by omega)]
  apply div_lt_div_of_pos_right _ (by exact_mod_cast Nat.factorial_pos (2*q+1))
  exact_mod_cast Finset.card_lt_card (show
    (Finset.range L).filter (· ∈ exactlyOneDivisorIn n (2*q+1)) ⊂
    (Finset.range L).filter (· ∈ exactlyOneDivisorIn n (2*q)) by
      have hqmem : q ∈ Set.Ioo n (2*q+1) := ⟨hq, by omega⟩
      have h2mem : 2*q ∈ Set.Ioo n (2*q+1) := ⟨by omega, by omega⟩
      have nodiv (x : ℕ) (hx : x ∈ exactlyOneDivisorIn n (2*q+1)) : ¬ 2*q ∣ x := by
        intro h
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hx
        have hxq : q ∈ ({a} : Set ℕ) := ha ▸ (show q ∈ {d ∈ Set.Ioo n (2*q+1) | d ∣ x} from ⟨hqmem, dvd_trans (dvd_mul_left q 2) h⟩)
        have hx2 : 2*q ∈ ({a} : Set ℕ) := ha ▸ (show 2*q ∈ {d ∈ Set.Ioo n (2*q+1) | d ∣ x} from ⟨h2mem, h⟩)
        simp only [Set.mem_singleton_iff] at hxq hx2
        omega
      constructor
      · intro x hx
        obtain ⟨hr,hx⟩ := Finset.mem_filter.mp hx
        have he : {d ∈ Set.Ioo n (2*q) | d ∣ x} = {d ∈ Set.Ioo n (2*q+1) | d ∣ x} := by
          ext d
          change ((n < d ∧ d < 2*q) ∧ d ∣ x) ↔ ((n < d ∧ d < 2*q+1) ∧ d ∣ x)
          have := nodiv x hx
          constructor
          · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨⟨h₁,by omega⟩,h₃⟩
          · rintro ⟨⟨h₁,h₂⟩,h₃⟩
            have hne : d ≠ 2*q := by rintro rfl; contradiction
            exact ⟨⟨h₁,by omega⟩,h₃⟩
        apply Finset.mem_filter.mpr
        exact ⟨hr, show {d ∈ Set.Ioo n (2*q) | d ∣ x}.ncard = 1 by rw [he]; exact hx⟩
      · intro hs
        have hm : 2*q ∈ exactlyOneDivisorIn n (2*q) := by
          apply Set.ncard_eq_one.mpr
          refine ⟨q, ?_⟩
          ext d
          change ((n < d ∧ d < 2*q) ∧ d ∣ 2*q) ↔ d = q
          constructor
          · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact factor_between hn hp h₁ h₂ h₃
          · rintro rfl; exact ⟨⟨hq,by omega⟩,dvd_mul_left _ _⟩
        exact nodiv _ (Finset.mem_filter.mp (hs (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hL, hm⟩))).2 dvd_rfl)

end CambieDrop

theorem OMA.solution : OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1.H2 := CambieDrop.drop

