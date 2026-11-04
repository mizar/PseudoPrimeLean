/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighFactorialComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowCumulative

/-! # History-safe cumulative bounds from the variable coefficients -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On `22 ≤ U ≤ V`, the paired radius coefficient is nondecreasing. Positive denominators
reduce the comparison to a rational inequality. -/
theorem pairedAlpha_mono {U V : ℝ} (hU : 22 ≤ U) (hUV : U ≤ V) : pairedAlpha U ≤ pairedAlpha V := by
  have hdu : 0 < (3 / 2 : ℝ) * U + 339 / 500 := by linarith only [hU]
  have hdv : 0 < (3 / 2 : ℝ) * V + 339 / 500 := by linarith only [hU, hUV]
  dsimp only [pairedAlpha]
  apply (div_le_div_iff₀ hdu hdv).mpr
  nlinarith only [hUV]

/-- On `22 ≤ U ≤ V`, the factorial radius coefficient is nondecreasing. Compare the two
positive-denominator fractions by cross-multiplication. -/
theorem factorialAlpha_mono {U V : ℝ} (hU : 22 ≤ U) (hUV : U ≤ V) :
    factorialAlpha U ≤ factorialAlpha V := by
  have hdu : 0 < (3 / 2 : ℝ) * U + 49 / 50 := by linarith only [hU]
  have hdv : 0 < (3 / 2 : ℝ) * V + 49 / 50 := by linarith only [hU, hUV]
  dsimp only [factorialAlpha]
  apply (div_le_div_iff₀ hdu hdv).mpr
  nlinarith only [hUV]

/-- The paired witness expression is nondecreasing in the logarithmic scale above `70000`.
Both its positive coefficient and the square of the scale are nondecreasing there. -/
theorem pairedBound_mono {L M : ℝ} (hL : 70000 ≤ L) (hLM : L ≤ M) :
    (pairedAlpha (2 * Real.log L)) ^ 2 * L ^ 2 ≤ (pairedAlpha (2 * Real.log M)) ^ 2 * M ^ 2 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hu := high_log_twice_ge_22 hL
  have hlog := Real.log_le_log hL0 hLM
  have hα := pairedAlpha_mono hu (show 2 * Real.log L ≤ 2 * Real.log M by linarith only [hlog])
  have ha0 := (pairedAlpha_bounds hu).1
  have ha0' : 0 ≤ pairedAlpha (2 * Real.log L) := by linarith only [ha0]
  have hs := pow_le_pow_left₀ hL0.le hLM 2
  have ha := pow_le_pow_left₀ ha0' hα 2
  exact mul_le_mul ha hs (sq_nonneg L) (sq_nonneg _)

/-- The factorial witness expression is nondecreasing in the logarithmic scale above `80000`.
This permits pointwise witnesses to be transferred to a common endpoint. -/
theorem factorialBound_mono {L M : ℝ} (hL : 80000 ≤ L) (hLM : L ≤ M) :
    (factorialAlpha (2 * Real.log L)) ^ 2 * L ^ 2 ≤
      (factorialAlpha (2 * Real.log M)) ^ 2 * M ^ 2 := by
  have h70 : (70000 : ℝ) ≤ L := by linarith only [hL]
  have hL0 : 0 < L := by linarith only [hL]
  have hu := high_log_twice_ge_22 h70
  have hlog := Real.log_le_log hL0 hLM
  have hα := factorialAlpha_mono hu (show 2 * Real.log L ≤ 2 * Real.log M by linarith only [hlog])
  have ha0 := (factorialAlpha_bounds hu).1
  have ha0' : 0 ≤ factorialAlpha (2 * Real.log L) := by linarith only [ha0]
  have hs := pow_le_pow_left₀ hL0.le hLM 2
  have ha := pow_le_pow_left₀ ha0' hα 2
  exact mul_le_mul ha hs (sq_nonneg L) (sq_nonneg _)

/-- The paired common-scale cap keeps the global four-ninths entrance bound for earlier inputs
and uses the nondecreasing paired witness expression for later inputs. -/
noncomputable def pairedCumulativeCap (L : ℝ) : ℝ :=
  max ((4 / 9 : ℝ) * (70000 : ℝ) ^ 2) ((pairedAlpha (2 * Real.log L)) ^ 2 * L ^ 2)

/-- The factorial common-scale cap keeps the paired bound at the `80000` entrance
for earlier inputs and uses the factorial witness expression for later inputs. -/
noncomputable def factorialCumulativeCap (L : ℝ) : ℝ :=
  max (pairedCumulativeCap 80000) ((factorialAlpha (2 * Real.log L)) ^ 2 * L ^ 2)

/-- Under GRH, the paired common-scale cap bounds the least rejecting prime of every odd
composite whose logarithm is at most `L`. The global bound covers pre-entrance inputs. -/
theorem leastPrime_le_pairedScale (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ pairedCumulativeCap L := by
  by_cases hhigh : (70000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := paired_prime_witness hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    exact
      ((Nat.cast_le.mpr hm).trans hb).trans ((pairedBound_mono hhigh hlog).trans (le_max_right _ _))
  · have hprev := leastPrime_le_fourNinthsScale hGRH hn ho hc 70000 (le_of_not_ge hhigh)
    exact hprev.trans ((min_le_right _ _).trans (le_max_left _ _))

/-- Under GRH, the factorial common-scale cap bounds the least rejecting prime of every odd
composite whose logarithm is at most `L`. The earlier high-coefficient bound covers the history. -/
theorem leastPrime_le_factorialScale (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ factorialCumulativeCap L := by
  by_cases hhigh : (80000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := factorial_prime_witness hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    exact
      ((Nat.cast_le.mpr hm).trans hb).trans
        ((factorialBound_mono hhigh hlog).trans (le_max_right _ _))
  · have hprev := leastPrime_le_pairedScale hGRH hn ho hc 80000 (le_of_not_ge hhigh)
    exact hprev.trans (le_max_left _ _)

/-- A history-safe cumulative bound intersects the previous cumulative envelope with the
paired and factorial common-scale bounds. The two constants cover all inputs before the
corresponding logarithmic entrances. -/
noncomputable def variableCumulative (N : ℕ) : ℝ :=
  min (highWindowCumulative N)
    (min (pairedCumulativeCap (Real.log N)) (factorialCumulativeCap (Real.log N)))

/-- Under GRH, the cumulative maximum of least rejecting prime bases is bounded by
`variableCumulative`. The proof combines the previous history with common-scale bounds and
retains a certified cap for inputs before each new entrance. -/
theorem cumulativeLeastPrime_le_variable
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ variableCumulative N := by
  have hp0 : ∀ L, 0 ≤ pairedCumulativeCap L := by
    intro L
    exact (by norm_num only : (0 : ℝ) ≤ (4 / 9) * (70000 : ℝ) ^ 2).trans (le_max_left _ _)
  have hf0 : ∀ L, 0 ≤ factorialCumulativeCap L := by
    intro L
    exact (hp0 80000).trans (le_max_left _ _)
  have hp :=
    cumulativeLeastPrime_le_base pairedCumulativeCap hp0
      (fun hn ho hc L hlog ↦ leastPrime_le_pairedScale hGRH hn ho hc L hlog) [] hGRH N
  have hf :=
    cumulativeLeastPrime_le_base factorialCumulativeCap hf0
      (fun hn ho hc L hlog ↦ leastPrime_le_factorialScale hGRH hn ho hc L hlog) [] hGRH N
  have hp' : (cumulativeLeastPrime N : ℝ) ≤ pairedCumulativeCap (Real.log N) := by
    simpa only [baseHistory] using hp
  have hf' : (cumulativeLeastPrime N : ℝ) ≤ factorialCumulativeCap (Real.log N) := by
    simpa only [baseHistory] using hf
  exact le_min (cumulativeLeastPrime_le_highWindow hGRH N) (le_min hp' hf')

end PseudoPrime.PrimeTestBounds.MillerRabin
