/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.MiddlePrefix
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.EnvelopeTransfer

/-! # Low psi Lee–Nosal estimate -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The unnormalized finite Lee–Nosal estimate for psi at x. -/
def psiEnvelope (x : ℝ) : Prop :=
  |Chebyshev.psi x - x| ≤
    Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi))

private theorem psiEnvelope_of_coeff {x c : ℝ} (hp : |Chebyshev.psi x - x| ≤ c * Real.sqrt x)
    (hc : c ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) :
    psiEnvelope x := by
  apply hp.trans
  rw [mul_comm c]
  exact mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg x)

private theorem checkedLow {a b m u v : ℕ} {s t : Edge} (ha : 0 < a) (hb : b ≤ 1000001)
    (ht : scale * m ≤ 1000 * (primeTicks gridTicks (gridTicks 32) a).1) (hm : (2 : ℝ) ≤ m / 1000)
    (hnum : 8 * (22 / 7) * (u / v : ℝ) ≤ (m / 1000 : ℝ) * (7 / 8 * (m / 1000 : ℝ) - 27 / 25))
    (extra : ℕ → ℕ) (count : ℕ) (h : batchAccepted a b extra (fun _ ↦ (u, v)) count s t = true) :
    Segment Valid psiEnvelope s t := by
  apply accepted_segment hb _ h
  intro n x hn _ hx _ hc
  exact
    psiEnvelope_of_coeff hc.1
      (coefficient_from_ticks ha ((Nat.cast_le.mpr hn).trans hx) ht hm
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hnum)

private def extra101 : ℕ → ℕ
  | 101 => 2
  | 104 => 3
  | 108 => 4
  | 113 => 7
  | 121 => 3
  | 125 => 1
  | 127 => 4
  | 132 => 5
  | 138 => 4
  | 143 => 4
  | _ => 0

private theorem part101 :
    Segment Valid psiEnvelope ⟨101, 94045306083764, 94045894722428, 10316920830281, 10316920830303⟩
      ⟨148, 141661030304900, 141662420709545, 15017401196067, 15017401196098⟩ := by
  apply
    checkedLow (a := 101) (b := 148) (m := 4614) (u := 271) (v := 500) (by decide) (by decide)
      (by decide +kernel) (by norm_num only) (by norm_num only) extra101 10
  decide +kernel

private def extra148 : ℕ → ℕ
  | 149 => 4
  | 154 => 4
  | 159 => 5
  | 165 => 4
  | 170 => 7
  | 178 => 4
  | 183 => 9
  | 193 => 5
  | 199 => 11
  | 211 => 9
  | _ => 0

private theorem part148 :
    Segment Valid psiEnvelope
      ⟨148, 141661030304900, 141662420709545, 15017401196067, 15017401196098⟩
      ⟨221, 211497687902277, 211500222870905, 17582350553525, 17582350553560⟩ := by
  apply
    checkedLow (a := 148) (b := 221) (m := 4996) (u := 327) (v := 500) (by decide) (by decide)
      (by decide +kernel) (by norm_num only) (by norm_num only) extra148 11
  decide +kernel

private def extra221 : ℕ → ℕ
  | 221 => 1
  | 223 => 4
  | 228 => 5
  | 234 => 6
  | _ => 0

private theorem part221 :
    Segment Valid psiEnvelope
      ⟨221, 211497687902277, 211500222870905, 17582350553525, 17582350553560⟩
      ⟨241, 238691031337871, 238693848669690, 17582350553525, 17582350553560⟩ := by
  apply
    checkedLow (a := 221) (b := 241) (m := 5397) (u := 781) (v := 1000) (by decide) (by decide)
      (by decide +kernel) (by norm_num only) (by norm_num only) extra221 4
  decide +kernel

/-- The shared prefix and the low logarithm comparisons give the psi envelope
for every real point from 101 up to the four-fifths cutoff. -/
theorem psi_envelope_low {x : ℝ} (hl : 101 ≤ x) (hr : x < 1423) : psiEnvelope x := by
  rcases lt_or_ge x 241 with hx | hx
  · exact ((segment_comp (segment_comp part101 part148) part221) low_prefix.1).2 x hl hx
  · have hc :=
      coefficient_from_ticks (n := 241) (m := 5483) (c := 81 / 100) (by decide) hx
        (by decide +kernel) (by norm_num only) (by norm_num only) (by norm_num only)
    exact psiEnvelope_of_coeff (middle_prefix.2 x hl hr) hc

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
