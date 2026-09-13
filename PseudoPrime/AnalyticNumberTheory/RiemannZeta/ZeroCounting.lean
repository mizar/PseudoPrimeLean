/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.Rectangle.Basic

/-!
# Meromorphicity and finite zeta zero ledgers

Zeta has finite meromorphic order everywhere. Away from its pole at one,
local factorization defines finite analytic multiplicities; at zeros these are
positive and yield a simple logarithmic-derivative pole. Compact sets, including
closed rectangles, have finite zero ledgers. No contour kernel is assumed.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

theorem meromorphic_riemannZeta : Meromorphic riemannZeta := by
  intro s
  by_cases hs : s = 1
  · subst s
    refine ⟨2, ?_⟩
    have heq : (fun z : ℂ ↦ (z - 1) ^ 2 • riemannZeta z) = fun z ↦ (z - 1) * riemannZeta₁ z := by
      funext z
      by_cases hz : z = 1
      · subst z
        simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, smul_eq_mul,
          zero_mul, riemannZeta₁_one, mul_one]
      · rw [riemannZeta_eq_inv_sub_mul hz]
        simp only [smul_eq_mul]
        field_simp [hz]
    rw [heq]
    exact (analyticAt_id.sub analyticAt_const).mul (differentiable_riemannZeta₁.analyticAt 1)
  · exact (analyticOn_riemannZeta s hs).meromorphicAt

/-- The meromorphic order of the Riemann zeta function is finite at every point. -/
theorem meromorphicOrderAt_riemannZeta_ne_top (s : ℂ) : meromorphicOrderAt riemannZeta s ≠ ⊤ := by
  have hanalyticZero : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 zero_ne_one
  have hzetaZero : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]; norm_num only
  have horderZero : meromorphicOrderAt riemannZeta 0 = 0 :=
    hanalyticZero.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hzetaZero
  apply
    (meromorphic_riemannZeta.exists_meromorphicOrderAt_ne_top_iff_forall.mp
        ?_)
      s
  exact
    ⟨0, by
      rw [horderZero];
      simp only [ne_eq, LinearOrderedAddCommGroupWithTop.zero_ne_top, not_false_eq_true]⟩

/-- The multiplicity of a zeta zero, expressed as its finite analytic vanishing order. -/
noncomputable def riemannZetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  analyticOrderNatAt riemannZeta ρ

/-- The analytic order of zeta is finite away from its pole at one. -/
theorem analyticOrderAt_riemannZeta_ne_top {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  have hanalytic : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  intro htop
  have hmero := hanalytic.meromorphicOrderAt_eq
  rw [htop] at hmero
  exact
    meromorphicOrderAt_riemannZeta_ne_top ρ
      (by simpa only [ENat.map_top] using hmero)

/-- Every zeta zero away from one has positive multiplicity. -/
theorem riemannZetaZeroMultiplicity_pos {ρ : ℂ} (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    0 < riemannZetaZeroMultiplicity ρ := by
  have hanalytic : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  have horder : analyticOrderAt riemannZeta ρ ≠ 0 := hanalytic.analyticOrderAt_ne_zero.mpr hzero
  have hfinite :=
    analyticOrderAt_riemannZeta_ne_top hρ1
  have hcast := Nat.cast_analyticOrderNatAt hfinite
  apply Nat.pos_of_ne_zero
  intro hmult
  have hmult' : analyticOrderNatAt riemannZeta ρ = 0 := by
    change analyticOrderNatAt riemannZeta ρ = 0 at hmult
    exact hmult
  apply horder
  rw [← hcast, hmult']
  simp only [CharP.cast_eq_zero]

/-- At any `ρ ≠ 1`, locally factor zeta as `(s-ρ)^m` times a nonvanishing
analytic function, where `m` is its analytic multiplicity. At nonzeros `m=0`. -/
theorem exists_riemannZeta_localFactor {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        riemannZeta =ᶠ[nhds ρ] fun s ↦
          (s - ρ) ^ riemannZetaZeroMultiplicity ρ •
            g s := by
  have hanalytic : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  simpa only [riemannZetaZeroMultiplicity] using
    hanalytic.analyticOrderAt_ne_top.mp
      (analyticOrderAt_riemannZeta_ne_top hρ1)

/--
Near a zeta zero, `ζ'/ζ` is its multiplicity divided by `s-ρ`, plus an analytic logarithmic
derivative.
-/
theorem exists_eventuallyEq_logDeriv_riemannZeta_at_zero {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    ∃ g : ℂ → ℂ,
      0 < riemannZetaZeroMultiplicity ρ ∧
        AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)) (logDeriv riemannZeta)
          (fun s ↦
            (riemannZetaZeroMultiplicity ρ : ℂ) /
                (s - ρ) +
              logDeriv g s) := by
  obtain ⟨g, hganalytic, hgzero, hfactor⟩ :=
    exists_riemannZeta_localFactor hρ1
  refine
    ⟨g, riemannZetaZeroMultiplicity_pos hρ1 hzero,
      hganalytic, hgzero, ?_⟩
  have hlog :
    Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)) (logDeriv riemannZeta)
      (logDeriv fun s ↦
        (s - ρ) ^ riemannZetaZeroMultiplicity ρ •
          g s) :=
    (logDeriv_congr_nhds hfactor).filter_mono nhdsWithin_le_nhds
  have hganalyticEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), AnalyticAt ℂ g s :=
    hganalytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hgzeroEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), g s ≠ 0 :=
    ((hganalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hgzero).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hlog, hganalyticEventually, hgzeroEventually, eventually_mem_nhdsWithin] with s
    hlogs hsanalytic hgs hsρ
  simp only [smul_eq_mul] at hlogs
  rw [hlogs]
  change
    logDeriv
        ((fun s ↦
            (s - ρ) ^ riemannZetaZeroMultiplicity ρ) *
          g)
        s =
      _
  rw [logDeriv_mul s]
  · rw [logDeriv_fun_pow (by fun_prop)]
    simp only [logDeriv_apply]
    rw [deriv_sub_const]
    simp only [deriv_id'', one_div, add_left_inj]
    ring
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsρ))
  · exact hgs
  · fun_prop
  · exact hsanalytic.differentiableAt

/--
At a finite-order zeta zero away from one, the zeta logarithmic derivative has a simple pole.

The finite-order hypothesis rules out local identically-zero behavior.  It is kept explicit here
so that the later zero ledger can discharge it once for every zero in a bounded contour.
-/
theorem meromorphicOrderAt_logDeriv_riemannZeta_eq_neg_one {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) (hfinite : meromorphicOrderAt riemannZeta ρ ≠ ⊤) :
    meromorphicOrderAt (logDeriv riemannZeta) ρ = -1 := by
  have hanalytic : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  have horder : meromorphicOrderAt riemannZeta ρ ≠ 0 := by
    intro horderZero
    have hne := hanalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp horderZero
    exact hne hzero
  exact meromorphicOrderAt_logDeriv_eq_neg_one hanalytic.meromorphicAt horder hfinite

/--
The pointwise quotient `ζ'/ζ` has a simple pole at every finite-order zeta zero away from one.
-/
theorem meromorphicOrderAt_riemannZeta_deriv_div_eq_neg_one {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) (hfinite : meromorphicOrderAt riemannZeta ρ ≠ ⊤) :
    meromorphicOrderAt (fun s ↦ deriv riemannZeta s / riemannZeta s) ρ = -1 := by
  change meromorphicOrderAt (logDeriv riemannZeta) ρ = -1
  exact
    meromorphicOrderAt_logDeriv_riemannZeta_eq_neg_one
      hρ1 hzero hfinite

/-- The zeta zeros in a compact set avoiding one form a finite set. -/
theorem finite_riemannZeta_zerosOn {K : Set ℂ} (hcompact : IsCompact K)
    (hone : K ⊆ ({1}ᶜ : Set ℂ)) : (K ∩ riemannZeta ⁻¹' {0}).Finite := by
  have hanalytic : AnalyticOnNhd ℂ riemannZeta K := analyticOn_riemannZeta.mono hone
  have hnormal : MeromorphicNFOn riemannZeta K := hanalytic.meromorphicNFOn
  rw [hnormal.zero_set_eq_divisor_support fun u ↦
      meromorphicOrderAt_riemannZeta_ne_top u]
  exact (MeromorphicOn.divisor riemannZeta K).finiteSupport hcompact

/-- The zeta zeros in any compact set form a finite set, even when the set contains the pole. -/
theorem finite_riemannZeta_zerosOn_compact {K : Set ℂ} (hcompact : IsCompact K) :
    (K ∩ riemannZeta ⁻¹' {0}).Finite := by
  let V : Set ℂ := K \ {1}
  have hVone : V ⊆ ({1}ᶜ : Set ℂ) := by
    intro s hs
    exact hs.2
  have hanalytic : AnalyticOnNhd ℂ riemannZeta V := analyticOn_riemannZeta.mono hVone
  have hnormal : MeromorphicNFOn riemannZeta V := hanalytic.meromorphicNFOn
  have hsupport : (Function.support (MeromorphicOn.divisor riemannZeta V)).Finite :=
    meromorphic_riemannZeta.meromorphicOn.divisor_support_finite_of_subset
      hcompact (fun _ hs ↦ hs.1)
  have hVfinite : (V ∩ riemannZeta ⁻¹' {0}).Finite := by
    rw [hnormal.zero_set_eq_divisor_support fun u ↦
        meromorphicOrderAt_riemannZeta_ne_top u]
    exact hsupport
  apply (hVfinite.union (Set.finite_singleton 1)).subset
  intro s hs
  by_cases hs1 : s = 1
  · exact Set.mem_union_right _ (Set.mem_singleton_iff.mpr hs1)
  · exact Set.mem_union_left _ ⟨⟨hs.1, hs1⟩, hs.2⟩

/-- The zeta zeros in a closed rectangle avoiding one form a finite set. -/
theorem finite_riemannZeta_zerosInRectangle {z w : ℂ}
    (hone : Rectangle.rectangleClosedBox z w ⊆ ({1}ᶜ : Set ℂ)) :
    (Rectangle.rectangleClosedBox z w ∩
        riemannZeta ⁻¹' {0}).Finite :=
  finite_riemannZeta_zerosOn
    (Rectangle.isCompact_rectangleClosedBox z w) hone

/-- The zeta zeros in an arbitrary closed rectangle form a finite set. -/
theorem finite_riemannZeta_zerosInAnyRectangle (z w : ℂ) :
    (Rectangle.rectangleClosedBox z w ∩
        riemannZeta ⁻¹' {0}).Finite :=
  finite_riemannZeta_zerosOn_compact
    (Rectangle.isCompact_rectangleClosedBox z w)

/--
The finite ledger of zeta zeros in a closed rectangle avoiding one.

The proof argument certifies that the rectangle contains no pole of zeta.  Each ledger entry can be
equipped with the local certificates proved above.
-/
noncomputable def riemannZetaZerosInRectangle (z w : ℂ)
    (hone : Rectangle.rectangleClosedBox z w ⊆ ({1}ᶜ : Set ℂ)) :
    Finset ℂ :=
  (finite_riemannZeta_zerosInRectangle hone).toFinset

/-- The finite zeta-zero ledger in an arbitrary closed rectangle. -/
noncomputable def riemannZetaZerosInAnyRectangle (z w : ℂ) : Finset ℂ :=
  (finite_riemannZeta_zerosInAnyRectangle z w).toFinset

/-- Membership in the rectangular zeta-zero ledger has the expected specification. -/
theorem mem_riemannZetaZerosInRectangle_iff {z w ρ : ℂ}
    {hone : Rectangle.rectangleClosedBox z w ⊆ ({1}ᶜ : Set ℂ)} :
    ρ ∈ riemannZetaZerosInRectangle z w hone ↔
      ρ ∈ Rectangle.rectangleClosedBox z w ∧
        riemannZeta ρ = 0 := by
  simp only [riemannZetaZerosInRectangle, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/-- Membership in the unrestricted rectangular zero ledger has the expected specification. -/
theorem mem_riemannZetaZerosInAnyRectangle_iff {z w ρ : ℂ} :
    ρ ∈ riemannZetaZerosInAnyRectangle z w ↔
      ρ ∈ Rectangle.rectangleClosedBox z w ∧
        riemannZeta ρ = 0 := by
  simp only [riemannZetaZerosInAnyRectangle, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/-- Every zero in the unrestricted rectangular ledger differs from zero. -/
theorem ne_zero_of_mem_riemannZetaZerosInAnyRectangle {z w ρ : ℂ}
    (hρ : ρ ∈ riemannZetaZerosInAnyRectangle z w) :
    ρ ≠ 0 := by
  intro hρzero
  rw [hρzero,
    mem_riemannZetaZerosInAnyRectangle_iff] at hρ
  have hzetaZero : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]; norm_num only
  exact hzetaZero hρ.2

/-- Every zero in the unrestricted rectangular ledger differs from one. -/
theorem ne_one_of_mem_riemannZetaZerosInAnyRectangle {z w ρ : ℂ}
    (hρ : ρ ∈ riemannZetaZerosInAnyRectangle z w) :
    ρ ≠ 1 := by
  intro hρone
  rw [hρone, mem_riemannZetaZerosInAnyRectangle_iff] at hρ
  exact riemannZeta_one_ne_zero hρ.2

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
