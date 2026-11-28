import Mathlib

/-!
# Constant payoff in absorbing games

Source: https://arxiv.org/abs/2003.02663 (M. Oliu-Barton, 2020), published as
Weighted-average stochastic games with constant payoff, Operational Research 22 (2022),
1675-1696, https://doi.org/10.1007/s12351-021-00625-6. The paper proves the
constant-payoff conjecture of Sorin, Venel and Vigeral for absorbing games (and, in the
published version, for smooth games) and says that the general case of finite zero-sum
stochastic games is open. The conjecture goes back to Sorin, Venel and Vigeral,
Asymptotic properties of optimal trajectories in dynamic programming, Sankhya A 72
(2010), Section 5.4, https://arxiv.org/abs/1012.5149.
Credit: @tatashbar

What is stated. For every evaluation with nonincreasing weights there are Markov
strategies of both players such that, as the largest weight tends to 0, these strategies
are approximately optimal and the expected payoff accumulated up to time t is
approximately t times the limit value, uniformly in t in [0,1]. Time is measured by the
accumulated weight, as in Section 2.2 of the source. The uniform bound in t is equivalent
to formula (1.1) of the published version, which takes the ratio of the accumulated
payoff to the accumulated weight along any stages M with accumulated weight bounded
away from 0.

Two points differ from Conjecture 1.1 of the published version (page 1678), which asks
for strategies of any kind and takes the limit over all sequences of weights whose
largest weight tends to 0.
* Nonincreasing weights. The limit over all weights cannot be meant literally: for two
  states that alternate with no choices and rewards 1 and 0, the weights 1/N on the
  stages 1, 3, ..., 2N - 1 give payoff 1, while the limit value is 1/2. Sorin, Venel and
  Vigeral ask for decreasing weights. This is read here as nonincreasing, so that the
  n-stage game is included.
* Markov strategies. Sorin, Venel and Vigeral ask for strategies that depend only on the
  elapsed time and the current state, and the source proves its results for an explicit
  Markov family (at stage m, play optimally for the discount factor equal to the weight
  of stage m divided by the sum of the weights from stage m on). Without this restriction
  the statement follows from known results: strategies that are approximately optimal in
  all long games (Mertens and Neyman, 1981) have the property for nonincreasing weights,
  by an Abel summation.

Known cases: the discounted evaluation (Catoni, Oliu-Barton and Ziliotto, 2021), the
n-stage evaluation (Ragel and Ziliotto, arXiv 2409.05683), absorbing and smooth games
(the source).

Conventions.
* Stages are indexed from 0 here; the papers index them from 1. So `w m` is the weight of
  the stage `m + 1` of the papers.
* A behavior strategy maps the list of past triples (state, action of player 1, action
  of player 2), most recent first, and the current state to a mixed action.
* Expected stage rewards are computed by a finite recursion over histories. This gives
  the expectation under the law of the play.
* The limit value `v` is the limit of the discounted values. It exists by Bewley and
  Kohlberg (1976); here it enters as a hypothesis.
-/

namespace OMA.S_arxiv_2003_02663

open Filter Topology

/-- A finite zero-sum stochastic game: `g k i j` is the stage reward to player 1 and
`q k i j l` the probability of moving from state `k` to state `l`. -/
structure Game (K I J : Type) [Fintype K] where
  g : K → I → J → ℝ
  q : K → I → J → K → ℝ
  q_nonneg : ∀ k i j l, 0 ≤ q k i j l
  q_sum : ∀ k i j, ∑ l, q k i j l = 1

/-- A behavior strategy with action set `A`. -/
structure Strategy (K I J A : Type) [Fintype A] where
  prob : List (K × I × J) → K → A → ℝ
  nonneg : ∀ h k a, 0 ≤ prob h k a
  sum_one : ∀ h k, ∑ a, prob h k a = 1

/-- A strategy is Markov if its mixed action depends only on the stage and the current
state. -/
def Strategy.IsMarkov {K I J A : Type} [Fintype A] (σ : Strategy K I J A) : Prop :=
  ∀ (h h' : List (K × I × J)) (k : K), h.length = h'.length → σ.prob h k = σ.prob h' k

/-- An evaluation: nonnegative stage weights with sum 1. -/
structure Evaluation where
  w : ℕ → ℝ
  nonneg : ∀ m, 0 ≤ w m
  hasSum : HasSum w 1

variable {K I J : Type} [Fintype K] [Fintype I] [Fintype J]

/-- The expected reward of the stage reached `m` stages after the history `h`, when the
current state is `k`. -/
noncomputable def stageReward (G : Game K I J) (σ : Strategy K I J I) (τ : Strategy K I J J) :
    ℕ → List (K × I × J) → K → ℝ
  | 0, h, k => ∑ i, ∑ j, σ.prob h k i * τ.prob h k j * G.g k i j
  | m + 1, h, k => ∑ i, ∑ j, σ.prob h k i * τ.prob h k j *
      ∑ l, G.q k i j l * stageReward G σ τ m ((k, i, j) :: h) l

/-- The expected weighted sum of the stage rewards from the initial state `k`. -/
noncomputable def payoff (G : Game K I J) (σ : Strategy K I J I) (τ : Strategy K I J J)
    (w : ℕ → ℝ) (k : K) : ℝ :=
  ∑' m, w m * stageReward G σ τ m [] k

/-- The payoff accumulated up to time `t`: the expected weighted sum of the rewards of
the stages $1,\dots,\varphi(\theta,t)$, where
$\varphi(\theta,t)=\inf\{M\ge 1:\sum_{m\le M}\theta_m\ge t\}$. Stage `m + 1` is included
exactly when no partial sum of the first `M` weights with `1 ≤ M ≤ m` has reached `t`. -/
noncomputable def headPayoff (G : Game K I J) (σ : Strategy K I J I) (τ : Strategy K I J J)
    (w : ℕ → ℝ) (k : K) (t : ℝ) : ℝ :=
  ∑' m, Set.indicator {m : ℕ | ∀ M, 1 ≤ M → M ≤ m → ∑ i ∈ Finset.range M, w i < t}
    (fun m => w m * stageReward G σ τ m [] k) m

/-- The max-min value of the discounted game with weights
$\lambda(1-\lambda)^{m-1}$. It is the value of that game by Shapley's theorem. -/
noncomputable def discountedValue (G : Game K I J) (lam : ℝ) (k : K) : ℝ :=
  ⨆ σ : Strategy K I J I, ⨅ τ : Strategy K I J J,
    payoff G σ τ (fun m => lam * (1 - lam) ^ m) k

/-- The constant-payoff conjecture for finite zero-sum stochastic games with a general
nonincreasing evaluation $\theta$. Let $v$ be the limit of the discounted values and
$k$ an initial state. There are Markov strategies $\sigma(\theta)$, $\tau(\theta)$ such
that for every $\varepsilon>0$ there is $\delta>0$ with the following property. If
$\theta$ is nonincreasing and all its weights are at most $\delta$, then $\sigma(\theta)$
guarantees $v^k-\varepsilon$, $\tau(\theta)$ guarantees $v^k+\varepsilon$, and the payoff
accumulated up to time $t$ under $(\sigma(\theta),\tau(\theta))$ is within $\varepsilon$
of $t\,v^k$ for all $t\in[0,1]$. -/
theorem main : ∀ (K I J : Type) [Fintype K] [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (G : Game K I J) (v : K → ℝ),
    (∀ k, Tendsto (fun lam : ℝ => discountedValue G lam k) (𝓝[>] 0) (𝓝 (v k))) →
    ∀ k : K, ∃ (σ : Evaluation → Strategy K I J I) (τ : Evaluation → Strategy K I J J),
      (∀ θ, (σ θ).IsMarkov ∧ (τ θ).IsMarkov) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ θ : Evaluation, Antitone θ.w → (∀ m, θ.w m ≤ δ) →
        (∀ τ' : Strategy K I J J, v k - ε ≤ payoff G (σ θ) τ' θ.w k) ∧
        (∀ σ' : Strategy K I J I, payoff G σ' (τ θ) θ.w k ≤ v k + ε) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, |headPayoff G (σ θ) (τ θ) θ.w k t - t * v k| ≤ ε := by
  sorry

end OMA.S_arxiv_2003_02663
