/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapFullEndpoint
public import PseudoPrime.LLS.ReciprocalGapEndpointLimit
public import PseudoPrime.LLS.ReciprocalGapEndpointWitness

/-! # Full-prime endpoint separation with the even reciprocal mass cap -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Scalar endpoint separation using the even reciprocal mass cap. The input `χ`
is assumed even in the witness theorem below; all other scalar parameters remain
explicit so the criterion can be reused independently of a radius choice. -/
noncomputable def reciprocalGapFullEndpointEvenSeparation (h : ℝ) (q : ℕ) (x Y : ℝ) : ℝ :=
  let M := reciprocalGapEvenReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))
  2 * M + reciprocalGapEndpointMassBudget h q x M + reciprocalGapSignedGammaBudget h x -
    (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
      (Real.sqrt x * (1 + h * Real.log x))

open AnalyticNumberTheory.RiemannZeta in
/-- Under primitive even nonprincipal GRH data, `h > 0` and `64 <= Y <= x`, a
negative even endpoint separation yields a prime `p <= x` with `χ(p) != 1`.
Assume no such prime, identify both finite character sums with their principal
counterparts, and compare the even reciprocal mass cap with the principal lower
bound. A prime dividing `q` remains an allowed witness. -/
theorem exists_prime_not_one_of_reciprocalGap_full_endpoint_even {h : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y)
    (hYx : Y ≤ x) (hgap : reciprocalGapFullEndpointEvenSeparation h q x Y < 0) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hp hpx
    by_contra hv
    exact hn ⟨p, hp, hpx, hv⟩
  have hy2 : (2 : ℝ) ≤ Y := by linarith only [hY]
  have he :=
    reciprocalSum_re_eq_of_full_prime_trivial χ (by linarith only [hy2] : 0 ≤ Y)
      (fun p hp hpy ↦ ht p hp (hpy.trans hYx))
  have hR := reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000 hGRH.riemann hy2
  rw [← he] at hR
  have hM := reciprocalGap_mass_le_even_reciprocal_cap hq hGRH hp hne heven hY hR
  have hU := reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH hp hne hinv hx.le hM
  have hL := logSum_div_le_gapSum hh hx.le (Finset.Ioc 0 ⌊x⌋₊) (fun _ hn ↦ hn)
  change
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x /
        (Real.sqrt x * (1 + h * Real.log x)) ≤
      _ at hL
  rw [← reciprocalGap_principal_re_eq_sum, ←
    reciprocalGapSum_re_eq_of_full_prime_trivial χ (zero_lt_one.trans hx).le ht] at hL
  have hd : 0 ≤ Real.sqrt x * (1 + h * Real.log x) :=
    mul_nonneg (Real.sqrt_nonneg x) (by nlinarith only [hh, Real.log_pos hx])
  have hl :=
    div_le_div_of_nonneg_right
      (PseudoPrime.LLS.logWeightedMangoldtSum_ge_rational_refined hGRH.riemann hx) hd
  dsimp only [reciprocalGapFullEndpointEvenSeparation] at hgap
  linarith only [hU, hL, hl, hgap]

/-- Right-limit scalar separation for the even reciprocal mass cap. The endpoint
mass is fixed as the gap tends to zero; only the normalized pole and signed Gamma
terms vary with `h`. -/
noncomputable def reciprocalGapFullEndpointEvenLimit (q : ℕ) (x Y : ℝ) : ℝ :=
  let M := reciprocalGapEvenReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))
  2 * M + (Real.log x * Real.log q / 2 + (Real.log x + 2) * M) / Real.sqrt x +
      ((9 / 2 : ℝ) * Real.sqrt x⁻¹ - (3 / 4 : ℝ) * Real.sqrt x⁻¹ * Real.log x) -
    (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) / Real.sqrt x

/-- The even endpoint separation converges to its stated limit as `h` decreases
to zero. Reuse the quotient and signed Gamma limits; the changed mass constant is
independent of `h`. -/
theorem tendsto_reciprocalGapFullEndpointEvenSeparation_right (q : ℕ) {x : ℝ} (hx : 1 ≤ x) (Y : ℝ) :
    Filter.Tendsto (fun h : ℝ ↦ reciprocalGapFullEndpointEvenSeparation h q x Y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (reciprocalGapFullEndpointEvenLimit q x Y)) := by
  let M := reciprocalGapEvenReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))
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
  dsimp only [reciprocalGapFullEndpointEvenSeparation, reciprocalGapEndpointMassBudget,
    reciprocalGapFullEndpointEvenLimit]
  exact ((tendsto_const_nhds.add hb).add (tendsto_reciprocalGapSignedGammaBudget_right hx)).sub hm

/-- A negative even endpoint limit yields a positive gap with negative separation.
Use right continuity of the separation at zero and the nontrivial right filter. -/
theorem exists_pos_gap_of_reciprocalGapFullEndpointEvenLimit_neg (q : ℕ) {x Y : ℝ} (hx : 1 ≤ x)
    (hlim : reciprocalGapFullEndpointEvenLimit q x Y < 0) :
    ∃ h : ℝ, 0 < h ∧ reciprocalGapFullEndpointEvenSeparation h q x Y < 0 := by
  have hn :
    ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), reciprocalGapFullEndpointEvenSeparation h q x Y < 0 :=
    (tendsto_reciprocalGapFullEndpointEvenSeparation_right q hx Y).eventually (Iio_mem_nhds hlim)
  have hp : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < h := self_mem_nhdsWithin
  exact (hp.and hn).exists

/-- For primitive even nonprincipal GRH data, a negative even endpoint limit at
`x >= 1` gives a non-one prime through `x`. Choose a positive gap and apply the
finite-gap endpoint witness theorem. -/
theorem exists_prime_not_one_of_reciprocalGapFullEndpointEvenLimit_neg {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y)
    (hYx : Y ≤ x) (hlim : reciprocalGapFullEndpointEvenLimit q x Y < 0) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  obtain ⟨h, hh, hs⟩ := exists_pos_gap_of_reciprocalGapFullEndpointEvenLimit_neg q hx.le hlim
  exact
    exists_prime_not_one_of_reciprocalGap_full_endpoint_even hh hq hGRH hp hne hinv heven hx hY hYx
      hs

/-- The even reciprocal mass cap and its right-limit separation are monotone in
the level. This transfers a negative estimate at the original level to any
primitive conductor dividing it. -/
theorem reciprocalGapFullEndpointEvenLimit_mono_level {x Y : ℝ} (hx : 1 ≤ x) (hY : 64 ≤ Y) {q N : ℕ}
    (hq : 0 < q) (hqN : q ≤ N) :
    reciprocalGapFullEndpointEvenLimit q x Y ≤ reciprocalGapFullEndpointEvenLimit N x Y := by
  have hy0 : 0 < Y := by linarith only [hY]
  have hy1 : 1 ≤ Y := by linarith only [hY]
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / Y) :=
    mul_nonneg (by norm_num only) (sub_nonneg.mpr ((div_le_one hy0).mpr hy1))
  have hl := Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqN)
  have hm :
    reciprocalGapEvenReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ)) ≤
      reciprocalGapEvenReciprocalMassCap N Y (Real.log Y - (31551 / 20000 : ℝ)) := by
    unfold reciprocalGapEvenReciprocalMassCap
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact
      sub_le_sub_right
        (sub_le_sub_right (mul_le_mul_of_nonneg_left (sub_le_sub_right hl (Real.log Real.pi)) hcoef)
          (179 / 200))
        _
  have hD : 0 ≤ Real.log x := Real.log_nonneg hx
  have hc : 0 ≤ Real.log x + 2 := by linarith only [hD]
  have hb :
    (Real.log x * Real.log q / 2 +
          (Real.log x + 2) *
            reciprocalGapEvenReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))) /
        Real.sqrt x ≤
      (Real.log x * Real.log N / 2 +
          (Real.log x + 2) *
            reciprocalGapEvenReciprocalMassCap N Y (Real.log Y - (31551 / 20000 : ℝ))) /
        Real.sqrt x := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg x)
    nlinarith only [hm, hl, hc, hD]
  unfold reciprocalGapFullEndpointEvenLimit
  dsimp only []
  linarith only [hm, hb]

end PseudoPrime.LLS.PaperStatements
