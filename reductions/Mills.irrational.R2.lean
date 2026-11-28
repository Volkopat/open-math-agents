import FormalConjectures.Wikipedia.Mills
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Irrationality of the least Mills number

A subquadratic prime interval above cubes, together with the two-factor
case of Ridout's theorem at 1, suffices. The interval hypothesis is shared
with the accepted reduction of Mills' existence theorem. The Diophantine
hypothesis is a specialization of the Roth–Ridout theorem already formalized
by the atlas-lean contributors and adapted by marcusbuffett for Erdős 240.

The proof records the floors of each infinite prime chain. A replacement
at one position can keep its entire prefix and continue through ordinary
cubic windows. Leastness then forces a small successor. Only infinitely
many narrow intervals along the floor sequence are needed for the
Diophantine contradiction.

The splicing argument follows the cubic case of K. Saito, *Mills' constant
is irrational*, Mathematika 71 (2025), e70027. The nested-interval construction
adapts caa1982's public proof of Mills.exists-prime.R1.H2.
-/

namespace MillsChain
open Real

/-- Nested Mills intervals realize every floor in a prescribed cubic chain.
Adapted from the accepted Mills.exists-prime.R1.H2 proof by caa1982. -/
theorem realize_chain (q : ℕ → ℕ) (hq2 : ∀ i,2 ≤ q i) (hlo : ∀ i,q i^3 ≤ q (i+1))
    (hhi : ∀ i,q (i+1)+1<(q i+1)^3) :
    ∃ A>(1:ℝ),∀ i : ℕ, ⌊A^(3^(i+1))⌋₊=q i := by
  let u : ℕ → ℝ := fun n => (q n : ℝ) ^ (((3 ^ (n + 1) : ℕ) : ℝ)⁻¹)
  let v : ℕ → ℝ := fun n => ((q n + 1 : ℕ) : ℝ) ^ (((3 ^ (n + 1) : ℕ) : ℝ)⁻¹)
  have hu_nonneg : ∀ n, 0 ≤ u n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hv_nonneg : ∀ n, 0 ≤ v n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hu_pow : ∀ n, u n ^ (3 ^ (n + 1)) = (q n : ℝ) := fun n =>
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by positivity)
  have hv_pow : ∀ n, v n ^ (3 ^ (n + 1)) = ((q n + 1 : ℕ) : ℝ) := fun n =>
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by positivity)
  have hu_mono : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    apply le_of_pow_le_pow_left₀ (show 3 ^ (n + 2) ≠ 0 by positivity) (hu_nonneg (n + 1))
    rw [show 3 ^ (n + 2) = 3 ^ (n + 1) * 3 by ring, pow_mul, hu_pow n,
      show 3 ^ (n + 1) * 3 = 3 ^ (n + 2) by ring, hu_pow (n + 1)]
    exact_mod_cast hlo n
  have hv_anti : StrictAnti v := by
    apply strictAnti_nat_of_succ_lt
    intro n
    apply lt_of_pow_lt_pow_left₀ (3 ^ (n + 2)) (hv_nonneg n)
    rw [hv_pow (n + 1), show 3 ^ (n + 2) = 3 ^ (n + 1) * 3 by ring, pow_mul, hv_pow n]
    exact_mod_cast hhi n
  have huv : ∀ n, u n < v n := by
    intro n
    apply lt_of_pow_lt_pow_left₀ (3 ^ (n + 1)) (hv_nonneg n)
    rw [hu_pow n, hv_pow n]
    push_cast
    linarith
  have huv_all : ∀ m n, u m < v n := by
    intro m n
    calc u m ≤ u (max m n) := hu_mono (le_max_left m n)
      _ < v (max m n) := huv (max m n)
      _ ≤ v n := hv_anti.antitone (le_max_right m n)
  have hbdd : BddAbove (Set.range u) := ⟨v 0, by rintro _ ⟨m, rfl⟩; exact (huv_all m 0).le⟩
  let A : ℝ := ⨆ m, u m
  have h1_lt_u0 : 1 < u 0 := by
    apply lt_of_pow_lt_pow_left₀ (3 ^ 1) (hu_nonneg 0)
    rw [one_pow, hu_pow 0]
    have : (2 : ℝ) ≤ q 0 := by exact_mod_cast hq2 0
    linarith
  have hA_ge : ∀ n, u n ≤ A := fun n => le_ciSup hbdd n
  have hA_lt : ∀ n, A < v n := by
    intro n
    have hle : A ≤ v (n + 1) := ciSup_le fun m => (huv_all m (n + 1)).le
    exact lt_of_le_of_lt hle (hv_anti (Nat.lt_succ_self n))
  refine ⟨A, lt_of_lt_of_le h1_lt_u0 (hA_ge 0), ?_⟩
  intro n
  have hA_nonneg : 0 ≤ A := le_trans (hu_nonneg 0) (hA_ge 0)
  have hlow : (q n : ℝ) ≤ A ^ (3 ^ (n + 1)) := by
    rw [← hu_pow n]
    exact pow_le_pow_left₀ (hu_nonneg n) (hA_ge n) _
  have hup : A ^ (3 ^ (n + 1)) < (q n : ℝ) + 1 := by
    have : A ^ (3 ^ (n + 1)) < v n ^ (3 ^ (n + 1)) :=
      pow_lt_pow_left₀ (hA_lt n) hA_nonneg (by positivity)
    rw [hv_pow n] at this
    push_cast at this
    exact this
  exact (Nat.floor_eq_iff (by positivity)).mpr ⟨hlow, hup⟩

end MillsChain

namespace MillsChain
open Mills

/-- The upper endpoint of the cubic floor interval cannot be one more
than a prime, since (p+1)^3−1 has p as a proper factor when p≥2. -/
theorem room_of_prime {p q : ℕ} (hp : 2 ≤ p) (prime : q.Prime) (lt : q<(p+1)^3) :
    q+1<(p+1)^3 := by
  by_contra! bad
  have eq : q+1=(p+1)^3 := by omega
  have e : q=p*(p^2+3*p+3) := by nlinarith only [eq]
  have dv : p∣q := ⟨_,e⟩
  have same : p=q := (prime.eq_one_or_self_of_dvd _ dv).resolve_left (by omega)
  have large : p < p*(p^2+3*p+3) :=
    by simpa using Nat.mul_lt_mul_of_pos_left (show 1 < p^2+3*p+3 by omega) (show 0 < p by omega)
  omega

/-- All successive floors of a Mills number have room for the strict
nested upper bound. -/
theorem prime_floors {A : ℝ} (one : 1 < A) (mills : IsMills A) :
    let p (j : ℕ) := ⌊A^(3^(j+1))⌋₊
    (∀ j,(p j).Prime) ∧ (∀ j,p j^3 ≤ p (j+1)) ∧ ∀ j,p (j+1)+1<(p j+1)^3 := by
  intro p
  have primes (j : ℕ) : (p j).Prime := Nat.prime_iff.mpr (mills ⟨j+1,by omega⟩)
  have pos : 0 ≤ A := by linarith
  have cube (j : ℕ) : A^(3^(j+1+1))=(A^(3^(j+1)))^3 := by rw [pow_succ 3 (j+1),pow_mul]
  refine ⟨primes,?_,?_⟩
  · intro j
    apply Nat.le_floor
    push_cast
    rw [cube]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (pow_nonneg pos _)) 3
  · intro j
    apply room_of_prime (primes j).two_le (primes (j+1))
    apply (Nat.floor_lt (pow_nonneg pos _)).mpr
    push_cast
    rw [cube]
    exact pow_lt_pow_left₀ (Nat.lt_floor_add_one _) (pow_nonneg pos _) (by decide)

/-- Replace a single successor in a prescribed prime floor chain, keep
every earlier floor, and extend the replacement to an infinite Mills branch. -/
theorem replace_successor (M : ℕ)
    (supply : ∀ p : ℕ,p.Prime → M ≤ p →
      ∃ t : ℕ,t.Prime ∧ p^3 ≤ t ∧ t+1<(p+1)^3)
    {A : ℝ} (one : 1 < A) (mills : IsMills A) (n q : ℕ) (prime : q.Prime) (eligible : M ≤ q)
    (lo : ⌊A^(3^(n+1))⌋₊^3 ≤ q) (hi : q+1<(⌊A^(3^(n+1))⌋₊+1)^3) :
    ∃ B>(1:ℝ),IsMills B ∧ (∀ j ≤ n,⌊B^(3^(j+1))⌋₊=⌊A^(3^(j+1))⌋₊) ∧
      ⌊B^(3^(n+2))⌋₊=q := by
  classical
  let p (i : ℕ) := ⌊A^(3^(i+1))⌋₊
  obtain ⟨primes,lows,highs⟩ := prime_floors one mills
  let S := {v : ℕ // v.Prime ∧ M ≤ v}
  have more (v : S) : ∃ b : S,v.val^3 ≤ b.val ∧ b.val+1<(v.val+1)^3 := by
    obtain ⟨t,pt,low,high⟩ := supply v.val v.property.1 v.property.2
    exact ⟨⟨t,pt,v.property.2.trans ((Nat.le_self_pow (by decide : 3≠0) _).trans low)⟩,low,high⟩
  choose nxt step using more
  let tail (j : ℕ) : S := (nxt^[j]) ⟨q,prime,eligible⟩
  have recurrence (j : ℕ) : tail (j+1)=nxt (tail j) := Function.iterate_succ_apply' ..
  let chain (i : ℕ) := if i ≤ n then p i else (tail (i-(n+1))).val
  have before {i : ℕ} (h : i ≤ n) : chain i=p i := if_pos h
  have after (j : ℕ) : chain (n+1+j)=(tail j).val := by
    simp only [chain,if_neg (by omega : ¬n+1+j ≤ n),Nat.add_sub_cancel_left]
  have allPrime (i : ℕ) : (chain i).Prime := by
    by_cases h : i ≤ n
    · rw [before h]; exact primes i
    · simpa only [chain,if_neg h] using (tail (i-(n+1))).property.1
  have edges (i : ℕ) : chain i^3 ≤ chain (i+1) ∧ chain (i+1)+1<(chain i+1)^3 := by
    rcases lt_trichotomy i n with earlier|rfl|later
    · rw [before earlier.le,before (by omega : i+1 ≤ n)]
      exact ⟨lows i,highs i⟩
    · have eq : chain (i+1)=q := after 0
      rw [before le_rfl,eq]
      exact ⟨lo,hi⟩
    · obtain ⟨j,rfl⟩ : ∃ j,i=n+1+j := ⟨i-(n+1),by omega⟩
      rw [after,show n+1+j+1=n+1+(j+1) by omega,after,recurrence]
      exact step (tail j)
  obtain ⟨B,gt,recorded⟩ := realize_chain chain (fun i => (allPrime i).two_le)
     (fun i => (edges i).1) (fun i => (edges i).2)
  refine ⟨B,gt,?_,fun j hj => (recorded j).trans (before hj), (recorded (n+1)).trans (after 0)⟩
  intro j
  obtain ⟨i,hi⟩ := j
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  change Prime ⌊B^(3^(k+1))⌋₊
  rw [recorded]; exact (allPrime k).prime

/-- At any index admitting continued prime growth, the successor of the
least Mills constant is no larger than any admissible prime replacement. -/
theorem least_successor (M : ℕ)
    (supply : ∀ p : ℕ,p.Prime → M ≤ p →
      ∃ t : ℕ,t.Prime ∧ p^3 ≤ t ∧ t+1<(p+1)^3)
    {A : ℝ} (least : IsMinMills A) (n q : ℕ) (prime : q.Prime) (eligible : M ≤ q)
    (lo : ⌊A^(3^(n+1))⌋₊^3 ≤ q) (hi : q+1<(⌊A^(3^(n+1))⌋₊+1)^3) :
    ⌊A^(3^(n+2))⌋₊ ≤ q := by
  obtain ⟨B,gt,mills,_,floor⟩ := replace_successor M supply least.1.1 least.1.2 n q prime eligible lo hi
  rw [← floor]
  exact Nat.floor_mono (pow_le_pow_left₀ (zero_le_one.trans least.1.1.le) (least.2 ⟨gt,mills⟩) _)

end MillsChain



namespace MillsChain
open Mills Filter Real

/-- The cubic floors eventually exceed every prescribed continuation threshold. -/
theorem floors_unbounded {A : ℝ} (one : 1 < A) (mills : IsMills A) :
    Tendsto (fun n : ℕ => ⌊A^(3^(n+1))⌋₊) atTop atTop := by
  let f (n : ℕ) := ⌊A^(3^(n+1))⌋₊
  obtain ⟨primes,lows,_⟩ := prime_floors one mills
  have grows (n : ℕ) : f n < f (n+1) := by
    have bigger : (f n)^1<(f n)^3 := (Nat.pow_lt_pow_iff_right (primes n).one_lt).mpr (by decide)
    exact (by simpa only [pow_one] using bigger : f n<(f n)^3).trans_le (lows n)
  exact (strictMono_nat_of_lt_succ grows).tendsto_atTop

theorem narrow_room {p q : ℕ} {s : ℝ} (p2 : 2 ≤ p) (smax : s≤2)
    (h : (q:ℝ)≤(p:ℝ)^3+(p:ℝ)^s) : q+1<(p+1)^3 := by
  have one : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have sq : (p:ℝ)^s≤(p:ℝ)^2 := by
    simpa only [rpow_ofNat] using rpow_le_rpow_of_exponent_le one smax
  have rr : (q:ℝ)+1<((p:ℝ)+1)^3 := by nlinarith [sq_nonneg (p:ℝ)]
  exact_mod_cast rr

/-- Continuations may use the whole cubic window. A narrow prime is needed
only at the unbounded family of indices where the sharper conclusion is desired. -/
theorem frequent_successor (s : ℝ) (smax : s≤2)
    (tails : ∀ᶠ p : ℕ in atTop,p.Prime → ∃ q : ℕ,q.Prime ∧ p^3 ≤ q ∧ q+1<(p+1)^3)
    {A : ℝ} (least : IsMinMills A)
    (short : ∃ᶠ n : ℕ in atTop,let p:=⌊A^(3^(n+1))⌋₊
      ∃ q : ℕ,p^3 < q ∧ (q:ℝ)≤(p:ℝ)^3+(p:ℝ)^s ∧ q.Prime) :
    ∃ᶠ n : ℕ in atTop,let p:=⌊A^(3^(n+1))⌋₊
      (⌊A^(3^(n+2))⌋₊:ℝ)≤(p:ℝ)^3+(p:ℝ)^s := by
  obtain ⟨M,supply⟩ := eventually_atTop.mp tails
  have large := (floors_unbounded least.1.1 least.1.2).eventually_ge_atTop M
  apply (short.and_eventually large).mono
  rintro n ⟨⟨q,lower,upper,prime⟩,eligible⟩
  let p := ⌊A^(3^(n+1))⌋₊
  have p2 := ((prime_floors least.1.1 least.1.2).1 n).two_le
  have mq : M ≤ q := eligible.trans ((Nat.le_self_pow (by decide : 3≠0) p).trans lower.le)
  have picked := least_successor M (fun p prime hp => supply p hp prime) least n q prime mq lower.le
    (narrow_room p2 smax upper)
  exact (show (⌊A^(3^(n+2))⌋₊:ℝ) ≤ q by exact_mod_cast picked).trans upper

/-- A global narrow-interval theorem implies both weaker requirements, including
frequent close successors on the specific floors of every Mills number. -/
theorem split_supply (s : ℝ) (smax : s≤2)
    (global : ∀ᶠ p : ℕ in atTop,∃ q : ℕ,p^3 < q ∧ (q:ℝ)≤(p:ℝ)^3+(p:ℝ)^s ∧ q.Prime) :
    (∀ᶠ p : ℕ in atTop,p.Prime → ∃ q : ℕ,q.Prime ∧ p^3 ≤ q ∧ q+1<(p+1)^3) ∧
    ∀ {A : ℝ},1 < A → IsMills A → ∃ᶠ n : ℕ in atTop,let p:=⌊A^(3^(n+1))⌋₊
      ∃ q : ℕ,p^3 < q ∧ (q:ℝ)≤(p:ℝ)^3+(p:ℝ)^s ∧ q.Prime := by
  refine ⟨?_,?_⟩
  · filter_upwards [global] with p h hp
    obtain ⟨q,lo,hi,prime⟩ := h
    exact ⟨q,prime,lo.le,narrow_room hp.two_le smax hi⟩
  · intro A one mills
    exact ((floors_unbounded one mills).eventually global).frequently

end MillsChain

namespace MillsApprox
open Filter

/-- At a floor of at least two, the cubic derivative saves the factor two in
the general estimate when the coefficient of the short interval is one. -/
theorem unit_cubic_gap {x θ : ℝ} (hx : 2 ≤ x) (nonneg : 0 ≤ θ)
    (succ : (⌊x^3⌋₊:ℝ) ≤ (⌊x⌋₊:ℝ)^3 + (⌊x⌋₊:ℝ)^θ) :
    x-(⌊x⌋₊:ℝ) < x^(θ-2) := by
  let p : ℝ := ⌊x⌋₊
  have p0 : 0 ≤ p := Nat.cast_nonneg _
  have p2 : (2:ℝ) ≤ p := by
    have h : 2≤⌊x⌋₊ := Nat.le_floor (by norm_cast)
    dsimp [p]; exact_mod_cast h
  have xp : 0 < x := by linarith
  have px : p ≤ x := Nat.floor_le xp.le
  have frac : x-p<1 := by have := Nat.lt_floor_add_one x; dsimp only [p]; linarith
  have pp : x ≤ p^2 := by nlinarith [sq_nonneg (p-2)]
  have den : x^2 ≤ x*p+p^2 := by nlinarith [mul_le_mul_of_nonneg_left frac.le xp.le]
  have fact : 2*((x-p)*x^2) ≤ x^3-p^3 := by
    nlinarith [mul_le_mul_of_nonneg_left den (sub_nonneg.mpr px)]
  have theta : p^θ ≤ x^θ := Real.rpow_le_rpow p0 px nonneg
  have one : 1 ≤ x^θ := Real.one_le_rpow (by linarith) nonneg
  have cube : x^3 < p^3+p^θ+1 := (Nat.lt_floor_add_one _).trans_le (add_le_add_left succ 1)
  change x-p < x^(θ-2)
  rw [Real.rpow_sub xp,show x^(2:ℝ)=x^2 by norm_cast]
  apply (lt_div_iff₀ (sq_pos_of_pos xp)).mpr
  linarith

/-- If the next cubic floor is prime, then the current argument is not an integer. -/
theorem positive_fraction {x : ℝ} (nonneg : 0 ≤ x) (prime : (⌊x^3⌋₊).Prime) :
    0 < x-(⌊x⌋₊:ℝ) := by
  by_contra! h
  have e : x=(⌊x⌋₊:ℝ) := le_antisymm (by linarith) (Nat.floor_le nonneg)
  have id : ⌊x^3⌋₊ = ⌊x⌋₊^3 := by
    conv_lhs => rw [e]
    rw [← Nat.cast_pow, Nat.floor_natCast]
  rw [id] at prime
  exact Nat.Prime.not_prime_pow (by decide : 2≤3) prime

end MillsApprox

namespace MillsApprox
open Filter

/-- An infinite subsequence of good successors suffices to approximate the
corresponding prime floors with the full exponential saving. -/
theorem frequent_prime_gap {A s : ℝ} (ha : 1 < A) (s0 : 0 ≤ s) (s2 : s < 2)
    (primes : ∀ n : ℕ, ⌊A^(3^(n+1) : ℕ)⌋₊.Prime)
    (succ : ∃ᶠ n : ℕ in atTop, let p := ⌊A^(3^(n+1) : ℕ)⌋₊
      (⌊A^(3^(n+2) : ℕ)⌋₊ : ℝ) ≤ (p : ℝ)^3 + (p : ℝ)^s) :
    let c := A^(s-2)
    0 < c ∧ c < 1 ∧ ∃ᶠ k : ℕ in atTop,
      (⌊A^(3^k : ℕ)⌋₊).Prime ∧
      0 < A^(3^k : ℕ) - (⌊A^(3^k : ℕ)⌋₊ : ℝ) ∧
      A^(3^k : ℕ) - (⌊A^(3^k : ℕ)⌋₊ : ℝ) < c^(3^k : ℕ) := by
  have pos : 0 < A := zero_lt_one.trans ha
  refine ⟨Real.rpow_pos_of_pos pos _, Real.rpow_lt_one_of_one_lt_of_neg ha (by linarith), ?_⟩
  refine frequently_atTop.mpr fun K => ?_
  obtain ⟨n, hn, step⟩ := frequently_atTop.mp succ K
  refine ⟨n+1, by omega, primes n, ?_⟩
  have next := primes (n+1)
  have power : A^(3^(n+2):ℕ)=(A^(3^(n+1):ℕ))^3 := by rw [pow_succ 3 (n+1), pow_mul]
  dsimp only at step
  rw [power] at step next
  have hxp := pow_pos pos (3^(n+1) : ℕ)
  have x2 : (2 : ℝ) ≤ A^(3^(n+1) : ℕ) :=
    (show (2 : ℝ) ≤ ⌊A^(3^(n+1) : ℕ)⌋₊ by exact_mod_cast (primes n).two_le).trans
      (Nat.floor_le hxp.le)
  exact ⟨positive_fraction hxp.le next,
    (unit_cubic_gap x2 s0 step).trans_eq (Real.rpow_pow_comm pos.le _ _).symm⟩

end MillsApprox

namespace MillsApprox
open Filter

/-- A continuation prime at every sufficiently large prime and a narrow prime
at infinitely many floors give prime approximants with exponentially small error. -/
theorem frequent_from_cubes (s : ℝ) (s0 : 0 ≤ s) (s2 : s < 2)
    (tails : ∀ᶠ p : ℕ in atTop, p.Prime →
      ∃ q : ℕ, q.Prime ∧ p^3 ≤ q ∧ q+1 < (p+1)^3)
    {A : ℝ} (least : Mills.IsMinMills A)
    (short : ∃ᶠ n : ℕ in atTop, let p := ⌊A^(3^(n+1) : ℕ)⌋₊
      ∃ q : ℕ, p^3 < q ∧ (q : ℝ) ≤ (p : ℝ)^3 + (p : ℝ)^s ∧ q.Prime) :
    let c := A^(s-2)
    0 < c ∧ c < 1 ∧ ∃ᶠ k : ℕ in atTop,
      (⌊A^(3^k : ℕ)⌋₊).Prime ∧
      0 < A^(3^k : ℕ) - (⌊A^(3^k : ℕ)⌋₊ : ℝ) ∧
      A^(3^k : ℕ) - (⌊A^(3^k : ℕ)⌋₊ : ℝ) < c^(3^k : ℕ) :=
  frequent_prime_gap least.1.1 s0 s2 (MillsChain.prime_floors least.1.1 least.1.2).1
    (MillsChain.frequent_successor s s2.le tails least short)

end MillsApprox

namespace MillsGap
open Filter Asymptotics Real

/-- The indexed standard bound on consecutive prime gaps gives a prime in
each short interval. The constant also covers the finitely many small x. -/
theorem intervals_of_prime_gaps (θ : ℝ) (hθ : 0 ≤ θ)
    (gap : (fun n : ℕ => ((Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)^θ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p:ℝ) ≤ x+C*(x:ℝ)^θ := by
  let P := Nat.nth Nat.Prime
  have mono : StrictMono P := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  obtain ⟨K,hK,large⟩ := gap.exists_pos
  obtain ⟨N,hN⟩ := eventually_atTop.1 large.bound
  let C := max K (P (N+1) : ℝ)
  have KC : K ≤ C := le_max_left .. 
  refine ⟨C,hK.trans_le KC,fun x hx => ?_⟩
  have x1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have pow1 : (1:ℝ)≤(x:ℝ)^θ := Real.one_le_rpow x1 hθ
  by_cases early : x < P N
  · refine ⟨P (N+1),Nat.prime_nth_prime _,early.trans (mono (Nat.lt_succ_self _)),?_⟩
    have upper : (P (N+1) : ℝ) ≤ C := le_max_right ..
    have posC : 0 ≤ C := hK.le.trans KC
    linarith [le_mul_of_one_le_right posC pow1]
  let k := Nat.count Nat.Prime (x+1)
  have next : x+1 ≤ P k := Nat.le_nth_count Nat.infinite_setOfPred_prime _
  have nz : k ≠ 0 := by
    intro e
    have at0 : P 0=2 := Nat.nth_prime_zero_eq_two
    rw [e,at0] at next
    omega
  let j := k-1
  have back : j+1=k := by dsimp [j]; omega
  have prev : P j ≤ x := Nat.le_of_lt_succ ((Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mp
    (show j < k from by omega))
  have NJ : N ≤ j := by
    by_contra! short
    have le : P (j+1) ≤ P N := mono.monotone short
    rw [back] at le
    omega
  have diff := hN j NJ
  change ‖((P (j+1)-P j : ℕ) : ℝ)‖ ≤ K * ‖(P j : ℝ)^θ‖ at diff
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Nat.cast_sub (mono (Nat.lt_succ_self _)).le] at diff
  have power : (P j : ℝ)^θ ≤ (x:ℝ)^θ := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast prev) hθ
  have term := mul_le_mul KC power (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hK.le.trans KC)
  refine ⟨P (j+1),Nat.prime_nth_prime _,back ▸ next,?_⟩
  linarith [show (P j : ℝ) ≤ x by exact_mod_cast prev]

/-- Absorb both the constant and the change of scale x=p³ into any
strictly larger exponent s. -/
theorem cube_intervals_of_intervals (θ s C : ℝ) (margin : 3*θ < s)
    (pr : ∀ x : ℕ, 2 ≤ x → ∃ q : ℕ, q.Prime ∧ x < q ∧ (q:ℝ) ≤ x+C*(x:ℝ)^θ) :
    ∀ᶠ p : ℕ in atTop, ∃ q : ℕ, p^3 < q ∧ (q:ℝ) ≤ (p:ℝ)^3+(p:ℝ)^s ∧ q.Prime := by
  have δ : 0 < s-3*θ := sub_pos.mpr margin
  obtain ⟨N,hN⟩ := exists_nat_ge ((max C 0) ^ (s-3*θ)⁻¹)
  filter_upwards [eventually_ge_atTop N,eventually_ge_atTop 2] with p large p2
  have bound := Real.rpow_le_rpow (Real.rpow_nonneg (le_max_right C 0) _)
    (hN.trans (show (N:ℝ) ≤ p by exact_mod_cast large)) δ.le
  rw [← Real.rpow_mul (le_max_right C 0), inv_mul_cancel₀ δ.ne', Real.rpow_one] at bound
  obtain ⟨q,prime,lq,uq⟩ := pr (p^3) (by nlinarith [Nat.pow_le_pow_left p2 3])
  have pos : 0<(p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  push_cast at uq
  have combine : ((p:ℝ)^3)^θ=(p:ℝ)^(3*θ) := by
    rw [← Real.rpow_natCast (p:ℝ) 3, ← Real.rpow_mul pos.le]
    norm_num
  have absorb' : C≤(p:ℝ)^(s-3*θ) := (le_max_left C 0).trans bound
  have step := mul_le_mul_of_nonneg_right absorb' (Real.rpow_nonneg pos.le (3*θ))
  rw [← Real.rpow_add pos, sub_add_cancel] at step
  exact ⟨q,lq,uq.trans (by rw [combine]; linarith),prime⟩


/-- An indexed exponent θ below s/3 gives a prime strictly after every
sufficiently large cube at distance at most p^s, with no constant factor. -/
theorem cube_intervals_of_prime_gaps (θ s : ℝ) (hθ : 0 ≤ θ) (margin : 3*θ < s)
    (gap : (fun n : ℕ => ((Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)^θ)) :
    ∀ᶠ p : ℕ in atTop, ∃ q : ℕ, p^3 < q ∧ (q:ℝ) ≤ (p:ℝ)^3+(p:ℝ)^s ∧ q.Prime := by
  obtain ⟨C,_,pr⟩ := intervals_of_prime_gaps θ hθ gap
  exact cube_intervals_of_intervals θ s C margin pr

/-- The same analytic proposition as H1 of the public Mills existence
reduction suffices for a genuinely subquadratic distance above cubes. -/
theorem subquadratic_cubes_of_ingham
    (cert : ∃ θ : ℝ, θ < 2 / 3 ∧ ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      ∃ q : ℕ, q.Prime ∧ x < q ∧ (q:ℝ) ≤ x+C*(x:ℝ)^θ) :
    ∃ s : ℝ, 0 < s ∧ s<2 ∧
      ∀ᶠ p : ℕ in atTop, ∃ q : ℕ, p^3 < q ∧ (q:ℝ) ≤ (p:ℝ)^3+(p:ℝ)^s ∧ q.Prime := by
  obtain ⟨θ,hθ,C,pr⟩ := cert
  let z := max θ 0
  have small : z<2/3 := max_lt hθ (by norm_num)
  have nonneg : 0 ≤ z := le_max_right ..
  have above : θ ≤ z := le_max_left ..
  exact ⟨(3*z+2)/2,by linarith,by linarith,
    cube_intervals_of_intervals θ _ C (by linarith) pr⟩

end MillsGap

namespace MillsDiophantine

/-- The large prime in the numerator introduces no cancellation against
the power of the fixed denominator. This includes exponent zero. -/
theorem prime_power_quotient {a b p : ℕ} (m : ℕ) (ha : 0 < a)
    (coprime : a.Coprime b) (prime : p.Prime) (large : a < p) :
    ∃ q : ℚ, q.num = ((p*b^m : ℕ) : ℤ) ∧ q.den = a^m ∧
      (q : ℝ)=(p : ℝ)*(b : ℝ)^m/(a : ℝ)^m := by
  have pc : p.Coprime a := prime.coprime_iff_not_dvd.mpr fun h =>
    (Nat.not_le_of_lt large) (Nat.le_of_dvd ha h)
  let q : ℚ := ⟨((p*b^m : ℕ) : ℤ), a^m, pow_ne_zero _ ha.ne',
    (pc.pow_right m).mul_left (coprime.symm.pow m m)⟩
  refine ⟨q,rfl,rfl,?_⟩
  rw [Rat.cast_def]
  change ((((p*b^m : ℕ) : ℤ) : ℝ) / ((a^m : ℕ) : ℝ))=_
  push_cast
  rfl

/-- A rational real number larger than one has a reduced representation
with positive natural denominator and strictly larger natural numerator. -/
theorem positive_fraction {A : ℝ} (large : 1 < A) (rational : ∃ q : ℚ, (q : ℝ)=A) :
    ∃ a b : ℕ, 0 < b ∧ b < a ∧ a.Coprime b ∧ A=(a : ℝ)/b := by
  obtain ⟨q,rfl⟩ := rational
  have hq : 1 < q := by exact_mod_cast large
  have hd : (q.den : ℤ) < q.num := by simpa using (Rat.lt_iff 1 q).mp hq
  have num : (q.num.natAbs : ℤ)=q.num :=
    Int.natAbs_of_nonneg (by have := q.den_pos; omega)
  refine ⟨q.num.natAbs,q.den,q.den_pos,?_,q.reduced,?_⟩
  · omega
  · have same : (q.num.natAbs : ℝ)=(q.num : ℝ) := by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) num
    rw [Rat.cast_def,same]

end MillsDiophantine

namespace MillsDiophantine
open Filter Finset

/-- The two divisibility factors at numerator and denominator in Ridout's
theorem exclude exponentially close large primes at rational powers. -/
theorem prime_mahler_of_ridout
    (ridout : ∀ (ε : ℝ), 0 < ε → ε≤1 → ∀ (p : Bool→ℕ) (μ ν : Bool→ℝ),
      (∀ l,0 ≤ μ l) → (∀ l,0 ≤ ν l) → (∑ l, (μ l+ν l))<2+ε →
      {q : ℚ | |1-(q:ℝ)|<1/(q.den:ℝ)^(2+ε-∑ l,(μ l+ν l)) ∧
        ∃ a b : Bool→ℕ, ((∏ l,p l^a l : ℕ):ℤ)∣q.num ∧ (∏ l,p l^b l)∣q.den ∧
        ∀ l,(q.den:ℝ)^(μ l)≤(p l:ℝ)^a l ∧ (q.den:ℝ)^(ν l)≤(p l:ℝ)^b l}.Finite)
    {a b : ℕ} (bpos : 0 < b) (ab : b < a) (cop : a.Coprime b)
    {ρ : ℝ} (rpos : 0 < ρ) (rsmall : ρ<1) :
    ∀ᶠ m : ℕ in atTop, ∀ p : ℕ, p.Prime → a < p →
      ρ^m ≤ |((a:ℝ)/b)^m-p| := by
  have a1 : (1:ℝ) < a := by exact_mod_cast (show 1 < a by omega)
  have a0 : (0:ℝ) < a := by positivity
  have b0 : (0:ℝ) < b := by exact_mod_cast bpos
  have b1 : (1:ℝ) ≤ b := by exact_mod_cast bpos
  have la := Real.log_pos a1
  have lb := Real.log_nonneg b1
  have lr := Real.log_neg rpos rsmall
  let w := Real.log b / Real.log a
  let ε := min 1 (-Real.log ρ / Real.log a)
  have epos : 0 < ε := lt_min zero_lt_one (div_pos (neg_pos.mpr lr) la)
  have e1 : ε≤1 := min_le_left _ _
  have emax : ε*Real.log a ≤ -Real.log ρ := (le_div_iff₀ la).mp (min_le_right ..)
  have wpos : 0 ≤ w := div_nonneg lb la.le
  have wle : w≤1 := (div_le_one la).mpr (Real.log_le_log b0 (by exact_mod_cast ab.le))
  have aw : (a:ℝ)^w=b := by
    rw [Real.rpow_def_of_pos a0,show Real.log a*w=Real.log b by dsimp [w]; field_simp]
    exact Real.exp_log b0
  have shrink : ρ≤1/(a:ℝ)^ε := by
    rw [Real.rpow_def_of_pos a0,one_div,←Real.exp_neg,←Real.exp_log rpos]
    exact Real.exp_le_exp.mpr (by linarith)
  let basis : Bool→ℕ := fun t => if t then a else b
  let μ : Bool→ℝ := fun t => if t then 0 else w
  let ν : Bool→ℝ := fun t => if t then 1 else 0
  have total : (∑ l, (μ l+ν l))=w+1 := by simp [μ,ν,add_comm]
  let S := {q : ℚ | |1-(q:ℝ)|<1/(q.den:ℝ)^(2+ε-∑ l,(μ l+ν l)) ∧
        ∃ c d : Bool→ℕ, ((∏ l,basis l^c l : ℕ):ℤ)∣q.num ∧ (∏ l,basis l^d l)∣q.den ∧
        ∀ l,(q.den:ℝ)^(μ l)≤(basis l:ℝ)^c l ∧ (q.den:ℝ)^(ν l)≤(basis l:ℝ)^d l}
  have finite : S.Finite := ridout ε epos e1 basis μ ν
    (fun t => by cases t <;> simp [μ,wpos]) (fun t => by cases t <;> simp [ν])
    (by rw [total]; linarith)
  obtain ⟨B,bound⟩ := (finite.image Rat.den).bddAbove
  filter_upwards [eventually_ge_atTop B] with m hm
  intro p prime large
  by_contra! short
  obtain ⟨q,num,den,value⟩ := prime_power_quotient m (by omega) cop prime large
  have member : q∈S := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · have scale : 1-(q:ℝ) = (((a:ℝ)/b)^m-p)*((b:ℝ)/a)^m := by
        rw [value,div_pow,div_pow]
        field_simp
      have weight : (1:ℝ)/((a:ℝ)^m)^(2+ε-(w+1)) = ((1/(a:ℝ)^ε)*((b:ℝ)/a))^m := by
        rw [←Real.rpow_pow_comm a0.le,←one_div_pow]
        congr 1
        rw [show 2+ε-(w+1)=1+ε-w by ring,Real.rpow_sub a0,Real.rpow_add a0,Real.rpow_one,aw]
        field_simp
      rw [den,Nat.cast_pow,total,scale,weight,abs_mul,abs_of_pos (pow_pos (div_pos b0 a0) _),mul_pow]
      exact mul_lt_mul_of_pos_right (short.trans_le (pow_le_pow_left₀ rpos.le shrink _)) (pow_pos (div_pos b0 a0) _)
    · exact fun t => if t then 0 else m
    · exact fun t => if t then m else 0
    · simp [basis,num]
    · simp [basis,den]
    · intro l
      cases l <;> simp [ν,μ,basis,den,←Real.rpow_pow_comm a0.le,aw]
  have small := bound (show q.den∈Rat.den '' S from ⟨q,member,rfl⟩)
  rw [den] at small
  have pow := Nat.lt_pow_self (n:=m) (a:=a) (by omega)
  omega

end MillsDiophantine

open Filter

namespace MillsDiophantine

/-- Only large prime integers, the actual Mills floors, are needed in the
separation estimate. The close approximation may hold merely frequently. -/
theorem irrational_of_prime_separation
    (separate : ∀ a b : ℕ, 0 < b → b < a → a.Coprime b → ∀ ρ : ℝ, 0 < ρ → ρ<1 →
      ∀ᶠ m : ℕ in atTop, ∀ p : ℕ, p.Prime → a < p → ρ^m ≤ |((a:ℝ)/b)^m-p|)
    {A : ℝ} (large : 1 < A) (prime : Mills.IsMills A) {ρ : ℝ} (rpos : 0 < ρ) (rsmall : ρ<1)
    (close : ∃ᶠ k : ℕ in atTop, A^(3^k:ℕ)-(⌊A^(3^k:ℕ)⌋₊:ℝ) < ρ^(3^k:ℕ)) :
    Irrational A := by
  rintro ⟨q,rat⟩
  obtain ⟨a,b,bpos,ab,cop,repr⟩ := positive_fraction large ⟨q,rat⟩
  have grow : Tendsto (fun k : ℕ => (3:ℕ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have floors := tendsto_nat_floor_atTop.comp ((tendsto_pow_atTop_atTop_of_one_lt large).comp grow)
  have far := grow.eventually (separate a b bpos ab cop ρ rpos rsmall)
  have all : ∀ᶠ k : ℕ in atTop,
      ρ^(3^k:ℕ) ≤ A^(3^k:ℕ)-(⌊A^(3^k:ℕ)⌋₊:ℝ) := by
    filter_upwards [far,floors.eventually_ge_atTop (a+1),eventually_ge_atTop 1] with k h enough hk
    have hp : Nat.Prime ⌊A^(3^k:ℕ)⌋₊ := Nat.prime_iff.mpr (prime ⟨k,hk⟩)
    change a+1 ≤ ⌊A^(3^k:ℕ)⌋₊ at enough
    have bound := h _ hp enough
    rw [←repr,abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le (pow_nonneg (by linarith) _)))] at bound
    exact bound
  exact close (all.mono fun _ h => not_lt.mpr h)

end MillsDiophantine

namespace MillsDiophantine
open Filter

/-- A frequently narrow next-prime interval at the actual least-Mills prime
floors is enough, provided the short-interval primes can be continued. -/
theorem irrational_of_sparse_prime_intervals
    (ridout : ∀ (ε : ℝ), 0 < ε → ε≤1 → ∀ (p : Bool→ℕ) (μ ν : Bool→ℝ),
      (∀ l,0 ≤ μ l) → (∀ l,0 ≤ ν l) → (∑ l, (μ l+ν l))<2+ε →
      {q : ℚ | |1-(q:ℝ)|<1/(q.den:ℝ)^(2+ε-∑ l,(μ l+ν l)) ∧
        ∃ a b : Bool→ℕ, ((∏ l,p l^a l : ℕ):ℤ)∣q.num ∧ (∏ l,p l^b l)∣q.den ∧
        ∀ l,(q.den:ℝ)^(μ l)≤(p l:ℝ)^a l ∧ (q.den:ℝ)^(ν l)≤(p l:ℝ)^b l}.Finite)
    (s : ℝ) (s0 : 0 ≤ s) (s2 : s<2)
    (tails : ∀ᶠ p : ℕ in atTop, p.Prime →
      ∃ q : ℕ, q.Prime ∧ p^3 ≤ q ∧ q+1<(p+1)^3)
    {A : ℝ} (least : Mills.IsMinMills A)
    (short : ∃ᶠ n : ℕ in atTop, let p := ⌊A^(3^(n+1):ℕ)⌋₊
      ∃ q : ℕ, p^3 < q ∧ (q:ℝ)≤(p:ℝ)^3+(p:ℝ)^s ∧ q.Prime) : Irrational A := by
  obtain ⟨rpos,rsmall,bound⟩ := MillsApprox.frequent_from_cubes s s0 s2 tails least short
  exact irrational_of_prime_separation (fun _ _ hb hab cop _ hρ hρ' =>
    prime_mahler_of_ridout ridout hb hab cop hρ hρ') least.1.1 least.1.2 rpos rsmall
    (bound.mono fun _ h => h.2.2)

end MillsDiophantine

namespace OMA.R_Mills_irrational_R2
open Filter Finset

/-- Ingham's prime interval bound with any exponent strictly below two thirds. -/
def H1 : Prop :=
  ∃ θ : ℝ, θ < 2 / 3 ∧ ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + C * (x : ℝ) ^ θ

/-- The Roth–Ridout finiteness theorem at the rational target 1, with two
divisibility factors in the numerator and denominator. -/
def H2 : Prop :=
  ∀ (ε : ℝ), 0 < ε → ε≤1 → ∀ (p : Bool→ℕ) (μ ν : Bool→ℝ),
      (∀ l,0 ≤ μ l) → (∀ l,0 ≤ ν l) → (∑ l, (μ l+ν l))<2+ε →
      {q : ℚ | |1-(q:ℝ)|<1/(q.den:ℝ)^(2+ε-∑ l,(μ l+ν l)) ∧
        ∃ a b : Bool→ℕ, ((∏ l,p l^a l : ℕ):ℤ)∣q.num ∧ (∏ l,p l^b l)∣q.den ∧
        ∀ l,(q.den:ℝ)^(μ l)≤(p l:ℝ)^a l ∧ (q.den:ℝ)^(ν l)≤(p l:ℝ)^b l}.Finite

theorem main : H1 → H2 → type_of% @Mills.irrational := by
  intro interval ridout A least
  obtain ⟨s,positive,small,uniform⟩ := MillsGap.subquadratic_cubes_of_ingham interval
  obtain ⟨tails,along⟩ := MillsChain.split_supply s small.le uniform
  exact MillsDiophantine.irrational_of_sparse_prime_intervals ridout s positive.le small
    tails least (along least.1.1 least.1.2)

end OMA.R_Mills_irrational_R2
