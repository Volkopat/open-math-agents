import OMAStatements.S_oeis_a077395

/-! A positive natural density for the squarefree sequence A077395.
The proof compares consecutive pairs with the corresponding pairs in a
periodic squarefree sieve. For positivity it counts consecutive squarefree
endpoints of distance three in a fixed arithmetic progression. The density
conjecture was posed by Thomas Ordowski and Robert Israel in 2015. -/

namespace SquarefreeDensity

noncomputable def count (s : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (· ∈ s)).card

noncomputable def freq (s : Set ℕ) (N : ℕ) : ℝ := (count s N : ℝ) / (N : ℝ)

end SquarefreeDensity

open Filter
open scoped Topology

namespace SquarefreeDensity

private lemma count_le_length (s : Set ℕ) (n : ℕ) : count s n ≤ n := by
  classical
  simpa [count] using (Finset.card_filter_le (Finset.range n) (· ∈ s))

/-- A periodic set has density equal to its frequency over one period. -/
theorem periodic_limit (s : Set ℕ) (P : ℕ) (hP : 0 < P)
    (per : ∀ n, n+P ∈ s ↔ n ∈ s) : Tendsto (freq s) atTop (𝓝 (freq s P)) := by
  classical
  have step (n : ℕ) : count s (n+P) = count s n + count s P := by
    simp only [count, ← Nat.count_eq_card_filter_range]
    rw [Nat.count_add']
    congr 1
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    exact Finset.filter_congr (fun i _ => per i)
  have block (r q : ℕ) : count s (r+q*P) = count s r + q*count s P := by
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.succ_mul, ← Nat.add_assoc, step, ih, Nat.succ_mul, Nat.add_assoc]
  have rate0 : 0 ≤ freq s P := by dsimp [freq]; positivity
  have rp : 0 < (P:ℝ) := by exact_mod_cast hP
  have rate1 : freq s P ≤ 1 := by
    rw [freq,div_le_one rp]
    exact_mod_cast count_le_length s P
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_const_div_atTop_nhds_zero_nat (P:ℝ)).eventually_lt_const hε)
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let r := n % P
  let q := n / P
  have decomp : r+q*P = n := by simpa [r,q,Nat.mul_comm] using Nat.mod_add_div n P
  have ct := block r q
  rw [decomp] at ct
  have ehr : (r:ℝ) ≤ P := by exact_mod_cast (Nat.mod_lt n hP).le
  have small : (count s r : ℝ) ≤ P := by exact_mod_cast (count_le_length s r).trans (Nat.mod_lt n hP).le
  have rem : |(count s r : ℝ) - (r:ℝ)*freq s P| ≤ P := by
    rw [abs_le]
    have hr : 0 ≤ (r:ℝ) := by positivity
    have hz : 0 ≤ (count s r : ℝ) := by positivity
    constructor <;> nlinarith [mul_nonneg hr rate0, mul_nonneg hr (sub_nonneg.mpr rate1)]
  have cr : (count s n : ℝ) = count s r + (q:ℝ)*count s P := by exact_mod_cast ct
  have nr : (r:ℝ)+(q:ℝ)*P = n := by exact_mod_cast decomp
  have pp : (P:ℝ) * freq s P = count s P := by rw [freq]; field_simp
  have diff : freq s n - freq s P = ((count s r : ℝ) - (r:ℝ)*freq s P) / n := by
    change (count s n : ℝ) / n - freq s P = _
    apply (eq_div_iff hn0.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hn0.ne']
    linear_combination cr + freq s P * nr - (q:ℝ)*pp
  rw [Real.dist_eq, diff, abs_div, abs_of_pos hn0]
  exact (div_le_div_of_nonneg_right rem hn0.le).trans_lt (hN n (by omega))

theorem periodic_approximation (T : Set ℕ)
    (approx : ∀ ε : ℝ, 0 < ε → ∃ S : Set ℕ,
      (∃ P : ℕ, 0 < P ∧ ∀ n, n+P ∈ S ↔ n ∈ S) ∧
      ∀ᶠ N in atTop, |freq T N - freq S N| ≤ ε) :
    ∃ L : ℝ, Tendsto (freq T) atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨S,⟨P,hP,per⟩,close⟩ := approx (ε/5) (by positivity)
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp close
  obtain ⟨N₂,hN₂⟩ := Metric.tendsto_atTop.mp (periodic_limit S P hP per) (ε/5) (by positivity)
  refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
  have hm₁ := hN₁ m (by omega)
  have hn₁ := hN₁ n (by omega)
  have hm₂ := hN₂ m (by omega)
  have hn₂ := hN₂ n (by omega)
  rw [Real.dist_eq] at hm₂ hn₂ ⊢
  linarith only [hε,hm₁,hn₁,hm₂,hn₂, abs_sub_le (freq T m) (freq S m) (freq T n),
    abs_sub_le (freq S m) (freq S P) (freq T n),
    abs_sub_le (freq S P) (freq S n) (freq T n),
    abs_sub_comm (freq S n) (freq S P), abs_sub_comm (freq T n) (freq S n)]

theorem of_count_error (T : Set ℕ)
    (approx : ∀ K : ℕ, 2 ≤ K → ∃ (S : Set ℕ) (P : ℕ) (C : ℝ),
      (∃ M : ℕ, 0 < M ∧ ∀ n, n+M ∈ S ↔ n ∈ S) ∧
      ∀ N : ℕ, |(count T N : ℝ) - count S N| ≤ 2*((N:ℝ)+P+1)/K+C) :
    ∃ L : ℝ, Tendsto (freq T) atTop (𝓝 L) := by
  apply periodic_approximation T
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt (4/ε)
  let K := k+2
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hKr : 0 < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
  have invK : 2/(K:ℝ) ≤ ε/2 := by
    have h := (div_lt_iff₀ hε).mp hk
    rw [div_le_iff₀ hKr]
    dsimp [K]
    push_cast
    nlinarith
  obtain ⟨S,P,C,periodic,bound⟩ := approx K hK
  refine ⟨S,periodic,?_⟩
  have tail := (tendsto_const_div_atTop_nhds_zero_nat (2*((P:ℝ)+1)/K+C)).eventually_lt_const
    (show (0:ℝ) < ε/2 by positivity)
  filter_upwards [tail,eventually_ge_atTop 1] with N htail hn
  have npos : 0 < (N:ℝ) := by exact_mod_cast hn
  change (2*((P:ℝ)+1)/K+C)/(N:ℝ) < ε/2 at htail
  calc
    _ = |(count T N : ℝ) - count S N| / N := by rw [freq, freq, ← sub_div,abs_div,abs_of_pos npos]
    _ ≤ (2*((N:ℝ)+P+1)/K+C) / N := div_le_div_of_nonneg_right (bound N) npos.le
    _ = 2/(K:ℝ) + (2*((P:ℝ)+1)/K+C)/(N:ℝ) := by field_simp; ring
    _ ≤ ε := by linarith

end SquarefreeDensity

open Finset
namespace SquarefreeDensity

/-- The periodic sieve omits multiples of prime squares up to a cutoff. -/
def sieve (K : ℕ) : Set ℕ := {x | ∀ p : ℕ, p.Prime → p ≤ K → ¬p*p ∣ x}

lemma squarefree_in_sieve (K : ℕ) {x : ℕ} (hx : Squarefree x) : x ∈ sieve K :=
  fun p hp _ => Nat.squarefree_iff_prime_squarefree.mp hx p hp

theorem sieve_periodic (K : ℕ) (n : ℕ) :
    n + K.factorial ^ 2 ∈ sieve K ↔ n ∈ sieve K := by
  have eqv (p : ℕ) (hp : p.Prime) (hle : p ≤ K) :
      p*p ∣ n + K.factorial ^ 2 ↔ p*p ∣ n := by
    have hd := Nat.dvd_factorial hp.pos hle
    rw [pow_two]
    exact (Nat.dvd_add_iff_left (Nat.mul_dvd_mul hd hd)).symm
  exact ⟨fun H p hp hle h => H p hp hle ((eqv p hp hle).mpr h),
    fun H p hp hle h => H p hp hle ((eqv p hp hle).mp h)⟩

private lemma count_positive_multiples (N m : ℕ) (hm : 0 < m) :
    ((range N).filter (fun x => 0 < x ∧ m ∣ x)).card ≤ N / m := by
  let s := (range N).filter (fun x => 0 < x ∧ m ∣ x)
  have h := card_le_card_of_injOn (s := s) (t := Ioc 0 (N/m)) (fun x => x/m)
  have maps : Set.MapsTo (fun x => x/m) (s : Set ℕ) (Ioc 0 (N/m) : Finset ℕ) := by
    intro x hx
    obtain ⟨xr,xp,xd⟩ := mem_filter.mp hx
    apply mem_Ioc.mpr
    exact ⟨Nat.div_pos (Nat.le_of_dvd xp xd) hm, Nat.div_le_div_right (mem_range.mp xr).le⟩
  have inj : Set.InjOn (fun x => x/m) (s : Set ℕ) := by
    intro x hx y hy eqn
    have xx := Nat.div_mul_cancel (mem_filter.mp hx).2.2
    have yy := Nat.div_mul_cancel (mem_filter.mp hy).2.2
    simpa only [xx,yy] using congrArg (· * m) eqn
  simpa using h maps inj

/-- The deleted numbers in the sieve have a uniformly small counting function. -/
theorem sieve_error (K N : ℕ) (hK : 2 ≤ K) :
    (count (sieve K \ {x | Squarefree x}) N : ℝ) ≤ (N : ℝ) / K := by
  classical
  let multiples (p : ℕ) := (range N).filter (fun x => 0 < x ∧ p*p ∣ x)
  have sub : (range N).filter (fun x => x ∈ sieve K \ {x | Squarefree x}) ⊆
      (Ioc K N).biUnion multiples := by
    intro x hx
    obtain ⟨hxN,hS,hn⟩ := mem_filter.mp hx
    have xp : 0 < x := by
      by_contra! h
      obtain rfl : x = 0 := by omega
      exact hS 2 Nat.prime_two hK (dvd_zero _)
    change ¬ Squarefree x at hn
    rw [Nat.squarefree_iff_prime_squarefree] at hn
    push Not at hn
    obtain ⟨p,hp,hd⟩ := hn
    have hpK : K < p := by by_contra! h; exact hS p hp h hd
    have hpn : p*p ≤ x := Nat.le_of_dvd xp hd
    have hz : p ≤ p*p := by nlinarith [hp.two_le]
    exact mem_biUnion.mpr ⟨p,mem_Ioc.mpr ⟨hpK,by have := mem_range.mp hxN; omega⟩,
      mem_filter.mpr ⟨hxN,xp,hd⟩⟩
  have cnt : count (sieve K \ {x | Squarefree x}) N ≤ ∑ p ∈ Ioc K N, N/(p*p) := by
    have cards : ∑ p ∈ Ioc K N, (multiples p).card ≤ ∑ p ∈ Ioc K N, N/(p*p) := by
      apply sum_le_sum
      intro p hp
      have hp0 : 0 < p := by have := (mem_Ioc.mp hp).1; omega
      exact count_positive_multiples N (p*p) (Nat.mul_pos hp0 hp0)
    have H := (card_le_card sub).trans (card_biUnion_le.trans cards)
    simpa [count] using H
  have invsum : ∑ p ∈ Ioc K N, ((p : ℝ)^2)⁻¹ ≤ (K:ℝ)⁻¹ := by
    by_cases h : K ≤ N
    · exact (sum_Ioc_inv_sq_le_sub (by omega : K ≠ 0) h).trans (sub_le_self _ (by positivity))
    · simp [Ioc_eq_empty_of_le (by omega : N ≤ K)]
  calc
    _ ≤ ((∑ p ∈ Ioc K N, N/(p*p) : ℕ) : ℝ) := by exact_mod_cast cnt
    _ ≤ ∑ p ∈ Ioc K N, (N:ℝ) * ((p:ℝ)^2)⁻¹ := by
      push_cast
      apply sum_le_sum
      intro p hp
      have hp0 : 0 < p := by have := (mem_Ioc.mp hp).1; omega
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (by positivity)).mpr
      rw [pow_two, ← Nat.cast_mul, ← Nat.cast_mul]
      exact_mod_cast Nat.div_mul_le_self N (p*p)
    _ = (N:ℝ) * ∑ p ∈ Ioc K N, ((p:ℝ)^2)⁻¹ := (mul_sum ..).symm
    _ ≤ _ := by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left invsum (Nat.cast_nonneg N)

end SquarefreeDensity

open Finset
namespace SquarefreeDensity

private def sf : Set ℕ := {x | Squarefree x}

private lemma arbitrarily_squarefree (n : ℕ) : ∃ m, n < m ∧ m ∈ sf := by
  obtain ⟨p, hp, hpr⟩ := Nat.exists_infinite_primes (n+1)
  exact ⟨p, hp, hpr.squarefree⟩

private noncomputable def gap (s : Set ℕ) (n : ℕ) : ℕ :=
  sInf {d : ℕ | 0 < d ∧ n+d ∈ s}

private lemma gap_spec {s : Set ℕ} (hu : ∀ n, ∃ m, n < m ∧ m ∈ s) (n : ℕ) :
    0 < gap s n ∧ n + gap s n ∈ s := by
  apply Nat.sInf_mem (s := {d : ℕ | 0 < d ∧ n+d ∈ s})
  obtain ⟨m,hm,hms⟩ := hu n
  exact ⟨m-n, by dsimp; exact ⟨by omega, by rwa [Nat.add_sub_of_le hm.le]⟩⟩

private lemma gap_le {s : Set ℕ} {d n : ℕ} (hd : 0 < d) (hs : n+d ∈ s) :
    gap s n ≤ d := Nat.sInf_le (show d ∈ {k : ℕ | 0 < k ∧ n+k ∈ s} from ⟨hd,hs⟩)

private def paired (s : Set ℕ) : Set ℕ := {n | n ∈ s ∧ ¬ n.Coprime (gap s n)}

private lemma pairing_is_termSet : paired sf = OMA.S_oeis_a077395.termSet := by
  ext n
  have hg := gap_spec arbitrarily_squarefree n
  have he : OMA.S_oeis_a077395.nextSquarefree n = n+gap sf n := by
    apply Nat.le_antisymm
    · exact Nat.sInf_le (show n+gap sf n ∈ {m : ℕ | n < m ∧ Squarefree m} from ⟨by omega,hg.2⟩)
    · have hx := Nat.sInf_mem (s := {m : ℕ | n < m ∧ Squarefree m}) (arbitrarily_squarefree n)
      change n < OMA.S_oeis_a077395.nextSquarefree n ∧ _ at hx
      have hm := gap_le (s := sf) (n := n) (d := OMA.S_oeis_a077395.nextSquarefree n - n)
        (by omega) (by rw [Nat.add_sub_of_le hx.1.le]; exact hx.2)
      omega
  change (Squarefree n ∧ ¬ n.Coprime (gap sf n)) ↔
    Squarefree n ∧ ¬Squarefree (n * OMA.S_oeis_a077395.nextSquarefree n)
  rw [he, Nat.squarefree_mul_iff]
  have hs : Squarefree (n+gap sf n) := hg.2
  simp [hs, Nat.coprime_self_add_right]
  tauto

private lemma gap_periodic {s : Set ℕ} {P : ℕ} (per : ∀ n, n+P ∈ s ↔ n ∈ s) (n : ℕ) :
    gap s (n+P) = gap s n := by
  unfold gap
  congr 1
  ext d
  change (0 < d ∧ (n+P)+d ∈ s) ↔ (0 < d ∧ n+d ∈ s)
  rw [show n+P+d=n+d+P by omega, per]

private lemma paired_periodic {s : Set ℕ} {P : ℕ} (hP : 0 < P)
    (hu : ∀ n, ∃ m, n < m ∧ m ∈ s) (per : ∀ n, n+P ∈ s ↔ n ∈ s) :
    ∃ M : ℕ, 0 < M ∧ ∀ n, n+M ∈ paired s ↔ n ∈ paired s := by
  let M := P.factorial * P
  have hiter (m n : ℕ) : n + m*P ∈ s ↔ n ∈ s := by
    induction m with
    | zero => simp
    | succ m ih => simp only [Nat.succ_mul, ← Nat.add_assoc, per, ih]
  have hM (n : ℕ) : n+M ∈ s ↔ n ∈ s := hiter _ _
  refine ⟨M, Nat.mul_pos P.factorial_pos hP, ?_⟩
  intro n
  change (n+M ∈ s ∧ ¬ (n+M).Coprime (gap s (n+M))) ↔ (n∈s ∧ ¬ n.Coprime (gap s n))
  rw [hM, gap_periodic hM]
  by_cases hs : n ∈ s
  · have hgap := gap_le hP ((per n).mpr hs)
    have hd : gap s n ∣ M := dvd_mul_of_dvd_left (Nat.dvd_factorial (gap_spec hu n).1 hgap) _
    obtain ⟨q,hq⟩ := hd
    simp [hs,hq,Nat.coprime_add_mul_left_left]
  · simp [hs]

/-- Each removed point changes at most its own pair and the pair starting at its predecessor. -/
private theorem pairing_error {s b : Set ℕ} {P : ℕ}
    (incl : s ⊆ b) (hu : ∀ n, ∃ m, n < m ∧ m ∈ s)
    (hP : 0 < P) (per : ∀ n, n+P ∈ b ↔ n ∈ b) (N : ℕ) :
    |(count (paired s) N : ℝ) - count (paired b) N| ≤ 2 * count (b \ s) (N+P) := by
  classical
  have hub (n : ℕ) : ∃ m, n < m ∧ m ∈ b := by
    obtain ⟨m, hm, hms⟩ := hu n
    exact ⟨m, hm, incl hms⟩
  let bad := (range (N+P)).filter (· ∈ b \ s)
  let prev := (range N).filter (fun n => n ∈ b ∧ n+gap b n ∈ bad)
  have next_strict {x y : ℕ} (hy : y ∈ b) (hlt : x < y) : x+gap b x < y+gap b y := by
    have h := gap_le (s := b) (n := x) (d := y-x) (by omega) (by rwa [Nat.add_sub_of_le hlt.le])
    have := (gap_spec hub y).1
    omega
  have hprev : prev.card ≤ bad.card := by
    apply card_le_card_of_injOn (fun n => n+gap b n)
    · intro n hn
      exact (mem_filter.mp hn).2.2
    · intro n hn m hm eqn
      rcases lt_trichotomy n m with h|h|h
      · exact ((next_strict (mem_filter.mp hm).2.1 h).ne eqn).elim
      · exact h
      · exact ((next_strict (mem_filter.mp hn).2.1 h).ne eqn.symm).elim
  have agreement (n : ℕ) (hn : n < N) (h0 : n ∉ bad) (h1 : n ∉ prev) :
      n ∈ paired s ↔ n ∈ paired b := by
    by_cases hb : n ∈ b
    · have hs : n ∈ s := by
        by_contra h
        exact h0 (mem_filter.mpr ⟨mem_range.mpr (by omega), hb, h⟩)
      have bound := gap_le hP ((per n).mpr hb)
      have hsb : n + gap b n ∈ s := by
        by_contra h
        exact h1 (mem_filter.mpr ⟨mem_range.mpr hn, hb, mem_filter.mpr
          ⟨mem_range.mpr (by omega), (gap_spec hub n).2, h⟩⟩)
      have eqn : gap s n = gap b n := le_antisymm (gap_le (gap_spec hub n).1 hsb)
        (gap_le (gap_spec hu n).1 (incl (gap_spec hu n).2))
      simp [paired,hs,hb,eqn]
    · have hs : n ∉ s := fun h => hb (incl h)
      simp [paired,hs,hb]
  have cover (x y : Set ℕ) (he : ∀ n < N, n ∉ bad → n ∉ prev → n ∈ x → n ∈ y) :
      count x N ≤ count y N + bad.card + prev.card := by
    let xs := (range N).filter (· ∈ x)
    let ys := (range N).filter (· ∈ y)
    have inc : xs ⊆ (ys ∪ bad) ∪ prev := by
      intro n hn
      have h := mem_filter.mp hn
      by_cases hp : n ∈ prev
      · exact mem_union_right _ hp
      by_cases hb : n ∈ bad
      · exact mem_union_left _ (mem_union_right _ hb)
      exact mem_union_left _ (mem_union_left _ (mem_filter.mpr
        ⟨h.1,he n (mem_range.mp h.1) hb hp h.2⟩))
    have h := (card_le_card inc).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    simpa [count,xs,ys] using h
  have h₁ := cover (paired s) (paired b) fun n h i j => (agreement n h i j).mp
  have h₂ := cover (paired b) (paired s) fun n h i j => (agreement n h i j).mpr
  have eqb : bad.card = count (b \ s) (N+P) := by simp [bad,count]
  rw [eqb] at hprev h₁ h₂
  rw [abs_le]
  constructor
  · have h : count (paired b) N ≤ 2 * count (b \ s) (N+P) + count (paired s) N := by omega
    linarith [show (count (paired b) N : ℝ) ≤ 2 * (count (b \ s) (N+P) : ℝ) +
      (count (paired s) N : ℝ) by exact_mod_cast h]
  · have h : count (paired s) N ≤ 2 * count (b \ s) (N+P) + count (paired b) N := by omega
    linarith [show (count (paired s) N : ℝ) ≤ 2 * (count (b \ s) (N+P) : ℝ) +
      (count (paired b) N : ℝ) by exact_mod_cast h]

theorem ordered_sieve (K : ℕ) (hK : 2 ≤ K) : ∃ S : Set ℕ, ∃ P : ℕ, ∃ C : ℝ,
    (∃ M : ℕ, 0 < M ∧ ∀ n, n+M ∈ S ↔ n∈S) ∧ ∀ N,
      |(count OMA.S_oeis_a077395.termSet N : ℝ) - count S N| ≤
        2 * ((N:ℝ)+P+1) / K + C := by
  have sub : sf ⊆ sieve K := fun _ hx => squarefree_in_sieve K hx
  have hu (n : ℕ) : ∃ m, n < m ∧ m ∈ sieve K := by
    obtain ⟨p,hp,hq⟩ := arbitrarily_squarefree n
    exact ⟨p,hp,sub hq⟩
  have pos : 0 < K.factorial ^ 2 := by positivity
  refine ⟨paired (sieve K),K.factorial^2,0,
    paired_periodic pos hu (sieve_periodic K), ?_⟩
  intro N
  rw [← pairing_is_termSet,add_zero]
  have h := pairing_error sub arbitrarily_squarefree pos (sieve_periodic K) N
  have e := sieve_error K (N+K.factorial^2) hK
  change (count (sieve K \ sf) (N+K.factorial^2) : ℝ) ≤ _ at e
  push_cast at e ⊢
  have hk : 0 < (K:ℝ) := by exact_mod_cast (show 0<K by omega)
  apply h.trans
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact e.trans (div_le_div_of_nonneg_right (by linarith) hk.le)

end SquarefreeDensity

open Finset Filter
open scoped Topology
namespace SquarefreeDensity
open OMA.S_oeis_a077395

/-- The two intermediate integers are divisible by 25 and 4 respectively.
The endpoints share the factor 3. -/
private lemma endpoints_mem (t : ℕ) (h0 : Squarefree (900*t+174)) (h3 : Squarefree (900*t+177)) :
    900*t+174 ∈ termSet := by
  let n := 900*t+174
  have hn1 : ¬Squarefree (n+1) := by
    intro h
    exact Nat.squarefree_iff_prime_squarefree.mp h 5 (by decide) (by dsimp [n]; omega)
  have hn2 : ¬Squarefree (n+2) := by
    intro h
    exact Nat.squarefree_iff_prime_squarefree.mp h 2 (by decide) (by dsimp [n]; omega)
  have he : nextSquarefree n = n+3 := by
    apply le_antisymm
    · apply Nat.sInf_le
      exact ⟨by omega, h3⟩
    · apply le_csInf ⟨n+3, (show n < n+3 ∧ Squarefree (n+3) from ⟨by omega,h3⟩)⟩
      intro m hm
      rcases hm with ⟨hlt, hsf⟩
      by_contra! h
      have : m = n+1 ∨ m = n+2 := by omega
      rcases this with rfl | rfl
      · exact hn1 hsf
      · exact hn2 hsf
  change Squarefree n ∧ ¬Squarefree (n * nextSquarefree n)
  rw [he]
  refine ⟨h0, fun h => Nat.squarefree_iff_prime_squarefree.mp h 3 (by decide) ?_⟩
  exact Nat.mul_dvd_mul (show 3 ∣ n by dsimp [n]; omega) (show 3 ∣ n+3 by dsimp [n]; omega)

/-- For each prime above 5, divisibility of the affine form occupies at
most one residue class, since its leading coefficient is a unit modulo p². -/
private lemma residue_bound (X p c : ℕ) (hp : p.Prime) (hl : 6 < p) :
    #((range X).filter fun t => p^2 ∣ 900*t+c) ≤ X/(p^2)+1 := by
  classical
  let B := (range X).filter fun t => p^2 ∣ 900*t+c
  change #B ≤ _
  rcases B.eq_empty_or_nonempty with h | ⟨v,hv⟩
  · simp [h]
  have hvd := (mem_filter.mp hv).2
  have hcop : Nat.Coprime (p^2) 900 := by
    apply Nat.Coprime.pow_left
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hd₁ := hp.dvd_of_dvd_pow (show p ∣ (2*3*5)^2 from hd)
    rw [hp.dvd_mul, hp.dvd_mul] at hd₁
    rcases hd₁ with ((hd|hd)|hd) <;> have := Nat.le_of_dvd (by decide) hd <;> omega
  have hs : B ⊆ (range X).filter (fun t => Nat.ModEq (p^2) t v) := by
    intro t ht
    obtain ⟨hr,hd⟩ := mem_filter.mp ht
    refine mem_filter.mpr ⟨hr, Nat.ModEq.cancel_left_of_coprime hcop ?_⟩
    apply Nat.ModEq.add_right_cancel' c
    exact (Nat.modEq_zero_iff_dvd.mpr hd).trans (Nat.modEq_zero_iff_dvd.mpr hvd).symm
  calc
    #B ≤ _ := card_le_card hs
    _ = _ := (Nat.count_eq_card_filter_range ..).symm
    _ ≤ X/(p^2)+1 := by
      rw [Nat.count_modEq_card X (pow_pos hp.pos 2) v]
      split <;> omega

/-- Restricting to n² indices puts every possible square divisor below
(31n+1)². Summing the rounding errors costs at most 31n+1. -/
private lemma bad_endpoint_bound (n c : ℕ) (hc : c = 174 ∨ c = 177) :
    (#((range (n^2)).filter fun t => ¬ Squarefree (900*t+c)) : ℝ)
      ≤ (n:ℝ)^2 * (2/7) + (31*n+1 : ℕ) := by
  classical
  let I := Ioo 6 (31*n+1)
  let P := I.filter Nat.Prime
  let B (p : ℕ) := (range (n^2)).filter fun t => p^2 ∣ 900*t+c
  have hs : ((range (n^2)).filter fun t => ¬ Squarefree (900*t+c)) ⊆ P.biUnion B := by
    intro t ht
    obtain ⟨ht, hsf⟩ := mem_filter.mp ht
    rw [Nat.squarefree_iff_prime_squarefree] at hsf
    push Not at hsf
    obtain ⟨p,hp,hpd⟩ := hsf
    have hlo : 6 < p := by
      by_contra! h
      rcases hc with rfl | rfl <;> interval_cases p <;> first | omega | norm_num at hp
    have hpos : 0 < 900*t+c := by rcases hc with rfl | rfl <;> omega
    have htlt := mem_range.mp ht
    have hsq := Nat.le_of_dvd hpos hpd
    have hp' : p < 31*n+1 := by
      by_contra! h
      have := Nat.mul_self_le_mul_self h
      rcases hc with rfl | rfl <;> nlinarith
    exact mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨mem_Ioo.mpr ⟨hlo,hp'⟩, hp⟩,
      mem_filter.mpr ⟨ht, by simpa [pow_two] using hpd⟩⟩
  have sug : (∑ p ∈ P, (((p:ℝ)^2)⁻¹)) ≤ 2/7 := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; positivity))
    convert (sum_Ioo_inv_sq_le (α := ℝ) 6 (31*n+1)) using 1
    norm_num
  have hcard : P.card ≤ 31*n+1 := by
    apply le_trans (card_le_card (filter_subset ..))
    simp [I, Nat.card_Ioo]
    omega
  have cap (p : ℕ) (hp : p ∈ P) :
      (#(B p) : ℝ) ≤ (n:ℝ)^2 * (((p:ℝ)^2)⁻¹) + 1 := by
    obtain ⟨hI,hprime⟩ := mem_filter.mp hp
    have hr := residue_bound (n^2) p c hprime (mem_Ioo.mp hI).1
    have pp : 0 < (p:ℝ) := by exact_mod_cast hprime.pos
    have hd : ((n^2 / p^2 : ℕ) : ℝ) ≤ (n:ℝ)^2/(p:ℝ)^2 := by
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast Nat.div_mul_le_self (n^2) (p^2)
    calc
      (#(B p) : ℝ) ≤ ((n^2/(p^2)+1 : ℕ) : ℝ) := by exact_mod_cast hr
      _ ≤ _ := by push_cast; simpa [div_eq_mul_inv] using add_le_add_right hd 1
  calc
    _ ≤ (#(P.biUnion B):ℝ) := by exact_mod_cast card_le_card hs
    _ ≤ ∑ p ∈ P, (#(B p):ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ p ∈ P, ((n:ℝ)^2 * (((p:ℝ)^2)⁻¹) + 1) := sum_le_sum cap
    _ = (n:ℝ)^2 * ∑ p ∈ P, (((p:ℝ)^2)⁻¹) + (P.card:ℝ) := by simp [sum_add_distrib,mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left sug (sq_nonneg _)) (by exact_mod_cast hcard)


private lemma frequency_at_squares (n : ℕ) (hn : 1000 ≤ n) :
    1/3600 ≤ freq termSet (900*n^2) := by
  classical
  let R := range (n^2)
  let B (c : ℕ) := R.filter (fun t => ¬ Squarefree (900*t+c))
  let G := R.filter (fun t => Squarefree (900*t+174) ∧ Squarefree (900*t+177))
  have cover : R ⊆ G ∪ (B 174 ∪ B 177) := by
    intro t ht
    by_cases h₀ : Squarefree (900*t+174)
    · by_cases h₃ : Squarefree (900*t+177)
      · exact mem_union_left _ (mem_filter.mpr ⟨ht,h₀,h₃⟩)
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨ht,h₃⟩))
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨ht,h₀⟩))
  have partition : n^2 ≤ G.card + ((B 174).card + (B 177).card) := by
    calc
      n^2 = R.card := (card_range _).symm
      _ ≤ _ := card_le_card cover
      _ ≤ _ := card_union_le ..
      _ ≤ _ := Nat.add_le_add_left (card_union_le ..) _
  have embed : G.image (fun t => 900*t+174) ⊆ (range (900*n^2)).filter (· ∈ termSet) := by
    intro z hz
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hz
    obtain ⟨ht',h0,h3⟩ := mem_filter.mp ht
    refine mem_filter.mpr ⟨mem_range.mpr ?_, endpoints_mem t h0 h3⟩
    have := mem_range.mp ht'
    omega
  have cardinal : G.card ≤ count termSet (900*n^2) := by
    change G.card ≤ #((range _).filter _)
    calc
      G.card = _ := (card_image_of_injective G (show Function.Injective (fun t : ℕ => 900*t+174)
          from fun u v h => by dsimp at h; omega)).symm
      _ ≤ _ := card_le_card embed
  have partitionR : (n:ℝ)^2 ≤ (G.card:ℝ) + (((B 174).card:ℝ) + ((B 177).card:ℝ)) := by
    exact_mod_cast partition
  have err (c : ℕ) (hc : c=174 ∨ c=177) :
      ((B c).card:ℝ) ≤ (n:ℝ)^2*(2/7) + (31*(n:ℝ)+1) := by
    simpa [B, R] using bad_endpoint_bound n c hc
  have positive : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have large : (1000:ℝ) ≤ n := by exact_mod_cast hn
  have lower : (n:ℝ)^2 / 4 ≤ (G.card:ℝ) := by
    nlinarith [err 174 (Or.inl rfl), err 177 (Or.inr rfl), mul_nonneg (sub_nonneg.mpr large) positive.le]
  have last : (G.card:ℝ) ≤ (count termSet (900*n^2):ℝ) := by exact_mod_cast cardinal
  unfold freq
  rw [le_div_iff₀ (by positivity)]
  push_cast
  linarith

theorem limit_lower_bound (L : ℝ) (h : Tendsto (freq termSet) atTop (𝓝 L)) : 1/3600 ≤ L := by
  by_contra! small
  have late := (tendsto_order.mp h).2 (1/3600) small
  obtain ⟨N,hN⟩ := eventually_atTop.mp late
  let n := max 1000 N
  have hn : 1000 ≤ n := le_max_left ..
  have hnN : N ≤ n := le_max_right ..
  have hN' : N ≤ 900*n^2 := by nlinarith [Nat.mul_self_le_mul_self hn]
  exact (not_lt_of_ge (frequency_at_squares n hn)) (hN _ hN')

theorem positive_of_limit (L : ℝ) (h : Tendsto (freq termSet) atTop (𝓝 L)) : 0 < L :=
  (show (0:ℝ) < 1/3600 by norm_num).trans_le (limit_lower_bound L h)

end SquarefreeDensity


open Filter
open scoped Topology

namespace SquarefreeDensity

/-- A positive counting density is the reciprocal growth rate along the increasing enumeration. -/
theorem enumeration (s : Set ℕ) (L : ℝ) (hL : 0 < L)
    (h : Tendsto (freq s) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)/(Nat.nth (· ∈ s) n : ℝ)) atTop (𝓝 L) := by
  classical
  have hInf : s.Infinite := by
    intro hf
    have hzero : Tendsto (freq s) atTop (𝓝 0) := by
      apply squeeze_zero (g := fun n : ℕ => (hf.toFinset.card:ℝ)/(n:ℝ))
      · intro n
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · intro n
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast Finset.card_le_card (show (Finset.range n).filter (· ∈ s) ⊆ hf.toFinset from
          fun i hi => hf.mem_toFinset.mpr (Finset.mem_filter.mp hi).2)
      · exact tendsto_const_div_atTop_nhds_zero_nat _
    exact hL.ne' (tendsto_nhds_unique h hzero)
  have hinf : (Set.ofPred (· ∈ s)).Infinite := hInf
  have cofinal : Tendsto (Nat.nth (· ∈ s)) atTop atTop :=
    (Nat.nth_strictMono hinf).tendsto_atTop
  have identity (n : ℕ) : count s (Nat.nth (· ∈ s) n) = n := by
    simpa [count, Nat.count_eq_card_filter_range] using Nat.count_nth_of_infinite hinf n
  have first : Tendsto (fun n : ℕ => (n:ℝ)/(Nat.nth (· ∈ s) n:ℝ)) atTop (𝓝 L) := by
    simpa [Function.comp_def, freq, identity] using h.comp cofinal
  have last := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp cofinal
  simpa [add_div, Function.comp_def] using first.add last

end SquarefreeDensity

theorem OMA.solution : type_of% @OMA.S_oeis_a077395.main := by
  obtain ⟨L, hL⟩ := SquarefreeDensity.of_count_error _ SquarefreeDensity.ordered_sieve
  have pos := SquarefreeDensity.positive_of_limit L hL
  exact ⟨L, pos, SquarefreeDensity.enumeration _ _ pos hL⟩
