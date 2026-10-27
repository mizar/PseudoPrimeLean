/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapFullEndpoint

/-! # Positive-gap limits for full endpoint witness separation -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For h>0,x>=1 the normalized conductor difference is at least
log(x)/(1+h*log x). Apply the scalar exponential-gap lower comparison.
Together with the existing upper bound, this controls the right limit without derivatives. -/
theorem reciprocalGapLogQuotient_ge_log_fraction {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) :
    Real.log x / (1 + h * Real.log x) ≤ reciprocalGapLogQuotient h x := by
  have he := exp_gap_ge_log_fraction hh (Real.log_nonneg hx)
  have hp : Real.exp (-h * Real.log x) = x ^ (-h) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx)]
    congr 1
    ring
  rw [hp] at he
  exact he

/-- For fixed x>=1 the conductor quotient tends to log(x) as h approaches zero
from the right. Squeeze between the rational lower bound and constant upper bound.
The totalized definition at h=0 need not equal this limit. -/
theorem tendsto_reciprocalGapLogQuotient_right {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto (fun h : ℝ ↦ reciprocalGapLogQuotient h x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.log x)) := by
  have hi : Filter.Tendsto (fun h : ℝ ↦ h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hd :
    Filter.Tendsto (fun h : ℝ ↦ 1 + h * Real.log x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa only [zero_mul, add_zero] using
      (tendsto_const_nhds.add (hi.mul tendsto_const_nhds) :
        Filter.Tendsto (fun h : ℝ ↦ 1 + h * Real.log x) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (1 + 0 * Real.log x)))
  have hl :
    Filter.Tendsto (fun h : ℝ ↦ Real.log x / (1 + h * Real.log x)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.log x)) := by
    simpa only [Pi.div_def, div_one] using
      (tendsto_const_nhds.div hd (by norm_num only : (1 : ℝ) ≠ 0))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · exact
      Filter.Eventually.mono self_mem_nhdsWithin
        (fun h hh ↦ reciprocalGapLogQuotient_ge_log_fraction hh hx)
  · exact
      Filter.Eventually.mono self_mem_nhdsWithin
        (fun h hh ↦ reciprocalGapLogQuotient_le_log hh (zero_lt_one.trans_le hx))

/-- For positive h and x>=1 the compact profile is sqrt(1/x) times the normalized
conductor quotient. Remove the clamp using nonnegativity and identify inverse powers.
This retains the signed Gamma saving in the positive-gap limit. -/
theorem reciprocalGapProfile_eq_logQuotient {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) :
    reciprocalGapProfile h x = Real.sqrt x⁻¹ * reciprocalGapLogQuotient h x := by
  have hp : x⁻¹ ^ h = x ^ (-h) := by
    rw [Real.inv_rpow (zero_le_one.trans hx), Real.rpow_neg (zero_le_one.trans hx)]
  have hn : 0 ≤ 1 - x ^ (-h) :=
    sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hh.le))
  unfold reciprocalGapProfile reciprocalGapLogQuotient
  rw [hp, max_eq_left hn]
  ring

/-- For fixed x>=1, the signed Gamma budget tends from the right to the displayed
logarithmic expression. Use the eventual profile identity and the quotient limit.
The negative logarithmic contribution is preserved. -/
theorem tendsto_reciprocalGapSignedGammaBudget_right {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto (fun h : ℝ ↦ reciprocalGapSignedGammaBudget h x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((9 / 2 : ℝ) * Real.sqrt x⁻¹ - (3 / 4 : ℝ) * Real.sqrt x⁻¹ * Real.log x)) := by
  have he :
    (fun h : ℝ ↦ reciprocalGapSignedGammaBudget h x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun h ↦
        (9 / 2 : ℝ) * Real.sqrt x⁻¹ -
          ((3 / 4 : ℝ) * Real.sqrt x⁻¹) * reciprocalGapLogQuotient h x) := by
    apply Filter.Eventually.mono self_mem_nhdsWithin
    intro h hh
    dsimp only [reciprocalGapSignedGammaBudget]
    rw [reciprocalGapProfile_eq_logQuotient hh hx]
    ring
  apply (Filter.tendsto_congr' he).2
  exact
    tendsto_const_nhds.sub
      ((tendsto_reciprocalGapLogQuotient_right hx).const_mul ((3 / 4 : ℝ) * Real.sqrt x⁻¹))

/-- The right-limit scalar separation for full-prime witnesses. Inputs q,x,Y
are totalized. It replaces the normalized difference by log(x), keeps the signed
Gamma saving and removes the positive-gap denominator. Negativity supplies a
sufficient witness criterion without choosing a gap. -/
noncomputable def reciprocalGapFullEndpointLimit (q : ℕ) (x Y : ℝ) : ℝ :=
  let M := reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))
  2 * M + (Real.log x * Real.log q / 2 + (Real.log x + 2) * M) / Real.sqrt x +
      ((9 / 2 : ℝ) * Real.sqrt x⁻¹ - (3 / 4 : ℝ) * Real.sqrt x⁻¹ * Real.log x) -
    (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) / Real.sqrt x

/-- For arbitrary q,Y and fixed x>=1, the full endpoint separation has the stated
right limit at zero gap. Combine the quotient and signed Gamma limits with the
nonzero limiting denominators. No limiting kernel or zero-sum exchange is assumed. -/
theorem tendsto_reciprocalGapFullEndpointSeparation_right (q : ℕ) {x : ℝ} (hx : 1 ≤ x) (Y : ℝ) :
    Filter.Tendsto (fun h : ℝ ↦ reciprocalGapFullEndpointSeparation h q x Y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (reciprocalGapFullEndpointLimit q x Y)) := by
  let M := reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))
  have hi : Filter.Tendsto (fun h : ℝ ↦ h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hD := tendsto_reciprocalGapLogQuotient_right hx
  have hd2 : Filter.Tendsto (fun h : ℝ ↦ 1 + 2 * h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (hi.const_mul 2) :
        Filter.Tendsto (fun h : ℝ ↦ 1 + 2 * h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 + 2 * 0)))
  have hc :
    Filter.Tendsto (fun h : ℝ ↦ (reciprocalGapLogQuotient h x + 2) / (1 + 2 * h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log x + 2)) := by
    simpa only [Pi.div_def, div_one] using
      ((hD.add_const 2).div hd2 (by norm_num only : (1 : ℝ) ≠ 0))
  have hb :=
    (((hD.mul_const (Real.log q)).div_const 2).add (hc.mul_const M)).div_const (Real.sqrt x)
  have hdl :
    Filter.Tendsto (fun h : ℝ ↦ 1 + h * Real.log x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa only [zero_mul, add_zero] using
      (tendsto_const_nhds.add (hi.mul_const (Real.log x)) :
        Filter.Tendsto (fun h : ℝ ↦ 1 + h * Real.log x) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (1 + 0 * Real.log x)))
  have hdmain :
    Filter.Tendsto (fun h : ℝ ↦ Real.sqrt x * (1 + h * Real.log x)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.sqrt x)) := by
    simpa only [mul_one] using hdl.const_mul (Real.sqrt x)
  have hm :
    Filter.Tendsto
      (fun h : ℝ ↦
        (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
          (Real.sqrt x * (1 + h * Real.log x)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) / Real.sqrt x)) := by
    simpa only [Pi.div_def] using
      (tendsto_const_nhds.div hdmain ((Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)).ne'))
  dsimp only [reciprocalGapFullEndpointSeparation, reciprocalGapEndpointMassBudget,
    reciprocalGapFullEndpointLimit]
  exact ((tendsto_const_nhds.add hb).add (tendsto_reciprocalGapSignedGammaBudget_right hx)).sub hm

/-- If the full endpoint limit is negative at x>=1, some positive gap has negative
separation. Strict inequality persists eventually along the nontrivial right filter.
This removes the need to supply or numerically tune a gap parameter. -/
theorem exists_pos_gap_of_fullEndpointLimit_neg (q : ℕ) {x Y : ℝ} (hx : 1 ≤ x)
    (hlim : reciprocalGapFullEndpointLimit q x Y < 0) :
    ∃ h : ℝ, 0 < h ∧ reciprocalGapFullEndpointSeparation h q x Y < 0 := by
  have hn : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), reciprocalGapFullEndpointSeparation h q x Y < 0 :=
    (tendsto_reciprocalGapFullEndpointSeparation_right q hx Y).eventually (Iio_mem_nhds hlim)
  have hp : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < h := self_mem_nhdsWithin
  exact (hp.and hn).exists

/-- For primitive nonprincipal GRH data at q>=2 and 64<=Y<=x, negativity of the
full endpoint limit yields a non-one prime at most x. Extract a positive gap and
apply the established witness theorem. No arithmetic supports or gap input remain. -/
theorem exists_prime_not_one_of_fullEndpointLimit_neg {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y)
    (hYx : Y ≤ x) (hlim : reciprocalGapFullEndpointLimit q x Y < 0) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  obtain ⟨h, hh, hs⟩ := exists_pos_gap_of_fullEndpointLimit_neg q hx.le hlim
  exact exists_prime_not_one_of_reciprocalGap_full_endpoint hh hq hGRH hp hne hinv hx hY hYx hs

end PseudoPrime.LLS.PaperStatements
