import OMAStatements.S_oeis_a111042
import Mathlib

-- 903 is an odd Erdos-Woods number (OEIS A111042, first term; counterexamples to Dowe's conjecture found
-- by Bienkowski, Korzeniowski and Lorys and by Lygeros, see Cegielski et al. 2003). The starting point a
-- below was found by our own search: a partition of the primes below 903 into P1, P2 such that every
-- i in [1, 902] has a prime factor in P1 or 903 - i has one in P2, then a = 0 (mod P1),
-- a = -903 (mod P2) by the Chinese remainder theorem. The 904 gcd conditions are checked by the kernel.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a111042.main) := by
  intro h
  have hw : OMA.S_oeis_a111042.Woods 903 :=
    ⟨by norm_num, 24220306346888432412903967737658519251789092126233778247004832733282836548838583703432414308006497937018708747922705991578498086430524063991081432091884650408040741215425842642714873581949617400000583455852847056473937546866750612520090716722689803330402028393273161989305334322492574386868929460636208127637122661285548979586741335391750348871146854148844906656845383105000,
      by norm_num, by decide +kernel⟩
  have he := h 903 hw
  exact absurd he (by decide)
