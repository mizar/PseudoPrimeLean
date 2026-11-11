/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsPhaseInputs
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundRiemannVonMangoldt
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGammaCellPrimitive

/-! # Coarse positive-height zero count under RH -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the positive-height zeta zero count differs from its standard
main term by at most `log t` for every `t ≥ 2πe`. The normalized count
identity, Gamma remainder and Backlund phase budget are all proved. -/
theorem positive_zero_count_log_of_RH (hRH : RiemannHypothesis) :
    ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
      |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
        Real.log t := by
  apply
    coarse_count_of_euler_phase
      (euler_phase_count_of_riemann_von_mangoldt (euler_riemann_von_mangoldt_of_RH hRH))
  intro t ht
  have hbase : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have hR :=
    gamma_remainder_bounds_of_integral
      (gamma_remainder_identity_of_complex backlund_gamma_complex_identity) t ht
  have hG := backlundTheta_error_of_signed_remainder (hbase.trans_le ht) hR.1 hR.2
  exact theta_error_le_of_phase (hbase.trans_le ht) hG

end PseudoPrime.PrimeTestBounds.MillerRabin
