/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsZeroCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundEulerLog
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundPhaseNumerics
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CoarseZeroCountNumerics

/-! # Three-elevenths bound from normalized phase inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The good-height zero-count identity in terms of an Euler-normalized
horizontal zeta argument and a real error function `E`. It states the
Riemann–von Mangoldt normalization needed to connect the Backlund phase bound
to the closed-height count; it does not assert this identity. -/
def EulerPhaseCountIdentity (E : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    2 * Real.pi * Real.exp 1 ≤ t →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) →
      ∀ φ : ℝ → ℝ,
        ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)) →
          (∀ x : ℝ,
            x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
              riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I) =
                (‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
                  Complex.exp ((φ x : ℂ) * Complex.I)) →
          φ (3 / 2) =
            (AnalyticNumberTheory.RiemannZeta.backlundZetaLog
                (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im →
          AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8) =
            φ (1 / 2) / Real.pi + E t

/-- If the normalized good-height counting identity holds with Gamma-phase
error at most `1/(5t)`, the coarse logarithmic zero-count estimate follows
at every height at least `2πe`. The Backlund argument estimate and the
right-limit transfer are proved internally. -/
theorem coarse_count_of_euler_phase {E : ℝ → ℝ} (hid : EulerPhaseCountIdentity E)
    (hE : ∀ t : ℝ, 2 * Real.pi * Real.exp 1 ≤ t → |E t| ≤ 1 / (5 * t)) :
    ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
      |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
        Real.log t := by
  apply AnalyticNumberTheory.RiemannZeta.positiveZeroCount_log_of_good_budget
  intro t ht hgood
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d2]
  have he : (163 / 60 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hpe := mul_le_mul hp he (by norm_num only : (0 : ℝ) ≤ 163 / 60) Real.pi_pos.le
  have ht17 : (17 : ℝ) ≤ t := by nlinarith only [hpe, ht]
  obtain ⟨φ, hc, hpolar, hnorm, hbound⟩ := exists_euler_arg_coarse ht17 hgood
  rw [hid t ht hgood φ hc hpolar hnorm]
  have hS : |φ (1 / 2) / Real.pi| ≤ (3 / 8 : ℝ) * Real.log t + 8 / 5 := by
    simpa only [abs_div, abs_of_pos Real.pi_pos] using hbound
  calc
    |φ (1 / 2) / Real.pi + E t| ≤ |φ (1 / 2) / Real.pi| + |E t| := abs_add_le _ _
    _ ≤ (3 / 8 : ℝ) * Real.log t + 8 / 5 + 1 / (5 * t) := add_le_add hS (hE t ht)

/-- Under GRH, the Euler-normalized good-height counting identity and the
stated Gamma-phase error bound imply the least-prime `3/11` witness bound for
every odd composite. The Backlund argument and coarse count are discharged
internally; the counting identity and Gamma error remain explicit inputs. -/
theorem three_eleven_least_of_euler_phase {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {E : ℝ → ℝ}
    (hid : EulerPhaseCountIdentity E)
    (hE : ∀ t : ℝ, 2 * Real.pi * Real.exp 1 ≤ t → |E t| ≤ 1 / (5 * t)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact three_eleven_least_of_coarse_count hn ho hc hGRH (coarse_count_of_euler_phase hid hE)

end PseudoPrime.PrimeTestBounds.MillerRabin
