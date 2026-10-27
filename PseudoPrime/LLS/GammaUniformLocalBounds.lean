/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSubgroupComparison
public import PseudoPrime.LLS.GammaTruncatedBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialCommonFactorCountBounds

/-! # Local-loss bounds for the uniform Gamma subgroup comparison

These theorems transfer prime-local counting to the actual principal-character
finite sums. No assumption excluding small prime factors is introduced.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For q ≠ 0, x > 0 and X ≥ 1, the principal finite level loss is at most
q.primeFactors.card * log X / sqrt x. Use the exact level-difference identity and
the prime-local count bound. This preserves the loss from primes dividing q. -/
theorem gamma_principal_level_loss_le_card_mul_log {q : ℕ} [NeZero q] {x X : ℝ} (hx : 0 < x)
    (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
      (q.primeFactors.card : ℝ) * Real.log X / Real.sqrt x := by
  rw [gamma_principal_sum_level_difference hx]
  exact
    div_le_div_of_nonneg_right
      (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum_le_card_mul_log (NeZero.ne q) hx
        hX)
      (Real.sqrt_nonneg x)

/-- For q ≠ 0, x > 0, X ≥ 1 and log q > 1, splitting at (log q)^(2/3)
bounds the principal finite level loss by the displayed logarithmic expression.
This supplies the uniform-subgroup modulus correction for general levels. -/
theorem gamma_principal_level_loss_le_log_two_thirds {q : ℕ} [NeZero q] {x X : ℝ} (hx : 0 < x)
    (hX : 1 ≤ X) (hL : 1 < Real.log q) :
    (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
      ((Real.log q) ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * Real.log q / Real.log (Real.log q)) * Real.log X /
        Real.sqrt x := by
  rw [gamma_principal_sum_level_difference hx]
  exact
    div_le_div_of_nonneg_right
      (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum_le_log_two_thirds (NeZero.ne q) hx
        hX hL)
      (Real.sqrt_nonneg x)

/-- Under RH, for q ≠ 0, x > 0, lambda ≥ 0, lambda*x ≥ 1 and log q > 1,
the finite principal Gamma sum has the displayed main term, error 13x^(1/4),
and split-prime loss. Combine the level-one lower bound with the exact correction.
This lower side can be used without small-prime or parity hypotheses. -/
theorem gamma_principal_sum_lower_log_two_thirds {q : ℕ} [NeZero q] (hRH : RiemannHypothesis)
    {x lambda : ℝ} (hx : 0 < x) (hl : 0 ≤ lambda) (hcut : 1 ≤ lambda * x) (hL : 1 < Real.log q) :
    Real.sqrt x * (1 - Real.exp (-lambda)) - 13 * x ^ (1 / 4 : ℝ) -
        ((Real.log q) ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * Real.log q / Real.log (Real.log q)) *
            Real.log (lambda * x) /
          Real.sqrt x ≤
      ∑ n ∈ Finset.Ioc 0 ⌊lambda * x⌋₊,
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re := by
  have hm := gamma_level_one_sum_lower_thirteen hRH hx hl
  have he := gamma_principal_level_loss_le_log_two_thirds (q := q) hx hcut hL
  linarith only [hm, he]

/-- Under GRH, q ≥ 20000, x ≥ 1, lambda ≥ 0, lambda*x ≥ 1 and log q > 1,
if all eligible primes through the cutoff lie in H, the displayed lower budget
is at most the conductor-sensitive primitive upper budget. Combine the finite
principal bound with the signed annihilator comparison, keeping the local loss. -/
theorem gamma_subgroup_comparison_log_two_thirds {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x lambda : ℝ} (hx : 1 ≤ x) (hl : 0 ≤ lambda) (hcut : 1 ≤ lambda * x) (hL : 1 < Real.log q)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    (H.index : ℝ) *
        (Real.sqrt x * (1 - Real.exp (-lambda)) - 13 * x ^ (1 / 4 : ℝ) -
          ((Real.log q) ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * Real.log q / Real.log (Real.log q)) *
              Real.log (lambda * x) /
            Real.sqrt x) ≤
      Real.sqrt x + 13 * x ^ (1 / 4 : ℝ) + (11783423 / 25000000 : ℝ) * subgroupConductorLogSum H +
        ((H.index - 1 : ℕ) : ℝ) * (39 + (10002 * Real.log q + 10004) / Real.sqrt x) := by
  have hm :=
    mul_le_mul_of_nonneg_left
      (gamma_principal_sum_lower_log_two_thirds hGRH.riemann (zero_lt_one.trans_le hx) hl hcut hL)
      (Nat.cast_nonneg H.index)
  have hu := gamma_principal_sum_le_conductor_bound_of_noSmallPrimes hq H hGRH hx hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he] at hu
  exact hm.trans hu

/-- Under the displayed scale and level conditions, GRH and a strict split-prime
budget gap yield a prime outside H coprime to q, through lambda*x. Contradict the
no-small-prime comparison. This connects the local-loss improvement to an actual
unit prime witness; numerical certification of the gap is a separate requirement. -/
theorem exists_prime_outside_of_gamma_split_gap {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x lambda : ℝ} (hx : 1 ≤ x) (hl : 0 ≤ lambda) (hcut : 1 ≤ lambda * x) (hL : 1 < Real.log q)
    (hgap :
      Real.sqrt x + 13 * x ^ (1 / 4 : ℝ) + (11783423 / 25000000 : ℝ) * subgroupConductorLogSum H +
          ((H.index - 1 : ℕ) : ℝ) * (39 + (10002 * Real.log q + 10004) / Real.sqrt x) <
        (H.index : ℝ) *
          (Real.sqrt x * (1 - Real.exp (-lambda)) - 13 * x ^ (1 / 4 : ℝ) -
            ((Real.log q) ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * Real.log q / Real.log (Real.log q)) *
                Real.log (lambda * x) /
              Real.sqrt x)) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ lambda * x ∧ ¬residueInSubgroup q H p := by
  classical
  by_contra hnone
  have hsmall (p : ℕ) (hp : p.Prime) (hd : ¬p ∣ q) (hle : (p : ℝ) ≤ lambda * x) :
    residueInSubgroup q H p := by
    by_contra hout
    exact hnone ⟨p, hp, hd, hle, hout⟩
  exact
    (not_le_of_gt hgap) (gamma_subgroup_comparison_log_two_thirds hq H hGRH hx hl hcut hL hsmall)

end PseudoPrime.LLS.PaperStatements
