/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ConductorSumBounds
public import PseudoPrime.LLS.MellinKernelTruncatedComparison
public import PseudoPrime.Analysis.LogSqrtErrorAbsorption
public import PseudoPrime.LLS.CosetPrimeBounds

/-! # Conductor-sensitive cutting-point and least-prime bounds

Retain the exact sum of primitive-conductor logarithms. The integral lower
bound and additive ambient allowances yield a least-prime estimate uniform
in subgroups and conductors, including conductors that remain bounded.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open Classical in
/-- Sum the logarithms of the primitive conductors of the nonprincipal
annihilator characters of H. This is the exact conductor cost retained in
the subgroup kernel comparison, instead of the common ambient logarithm. -/
noncomputable def subgroupConductorLogSum {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H), Real.log χ.val.conductor

/-- Each conductor logarithm is nonnegative, so the total conductor cost is
nonnegative. This permits uniform cutting-point bounds even when conductors
remain bounded as the ambient modulus grows. -/
theorem subgroupConductorLogSum_nonneg {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) :
    0 ≤ subgroupConductorLogSum H := by
  classical exact Finset.sum_nonneg (fun χ _ ↦ Real.log_natCast_nonneg χ.val.conductor)

/-- Each primitive conductor divides the nonzero ambient level and is at
most that level. Sum logarithmic monotonicity over the nonprincipal
annihilator characters, whose number is the subgroup index minus one.
This bounds the conductor cost by the ambient logarithmic cost. -/
theorem subgroupConductorLogSum_le {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) :
    subgroupConductorLogSum H ≤ ((H.index : ℝ) - 1) * Real.log q := by
  classical
  have hb : ∀ χ : NumberTheory.subgroupAnnihilator H, Real.log χ.val.conductor ≤ Real.log q := by
    intro χ
    have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.val.conductor_dvd_level
    exact
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.val.conductor_ne_zero)
        (by exact_mod_cast hd)
  have hs :=
    Finset.sum_le_sum
      (fun χ (_ : χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H)) ↦ hb χ)
  have hcard :
    ((Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H)).card : ℝ) =
      (H.index : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))),
      Nat.cast_one, NumberTheory.card_subgroupAnnihilator]
  simpa only [subgroupConductorLogSum, Finset.sum_const, nsmul_eq_mul, hcard] using hs

namespace MellinKernel

/-- At sufficiently large scales with sqrt x bounded by d log q, the
no-small-outside-prime hypothesis bounds the kernel main coefficient times
sqrt x by the exact conductor cost plus an arbitrarily small ambient
logarithmic allowance. Combine the finite upper and integral lower bounds;
reserve one quarter each for the integral loss and the two analytic errors. -/
theorem exists_conductor_comparison_scale (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h : ℕ} (hh : 1 < h) {b d ε : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∃ T : ℝ,
          2 ≤ T ∧
            ∀ (q : ℕ) [NeZero q],
              Q ≤ q →
                ∀ (H : Subgroup (ZMod q)ˣ),
                  H.index = h →
                    ∀ x : ℝ,
                      T ≤ x →
                        Real.sqrt x ≤ d * Real.log q →
                        (∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ b * x → residueInSubgroup q H p) →
                        ((h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) -
                              (K.function (1 / 2)).re) *
                            Real.sqrt x ≤
                          K.mass * subgroupConductorLogSum H + ε * Real.log q := by
  have hhR : (1 : ℝ) < h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := zero_lt_one.trans hhR
  obtain ⟨Cu, hCu, hu⟩ := exists_uniform_principal_sum_le_conductor_sum_of_noSmallPrimes K hg
  obtain ⟨Cl, hCl, hl⟩ := exists_eventually_principal_sum_ge_integral K hg.riemann
  let C := Cu + Cl
  have hC : 0 < C := add_pos hCu hCl
  let δ := ε / (4 * (h : ℝ) * d)
  have hδ : 0 < δ := div_pos hε (mul_pos (mul_pos (by norm_num only) hh0) hd)
  obtain ⟨Qu, hQu, hupper⟩ :=
    hu (ε / (4 * ((h : ℝ) - 1))) (div_pos hε (mul_pos (by norm_num only) (sub_pos.mpr hhR)))
  obtain ⟨Tl, hTl⟩ := Filter.eventually_atTop.mp (hl hb hδ)
  obtain ⟨Tn, hTn, hn⟩ :=
    Analysis.exists_error_absorption_scale hh0 hC (by norm_num only : (0 : ℝ) < 1) hε
  have hlog :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (8 * (h : ℝ) * C / ε)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hlog
  refine ⟨max Qu R, hQu.trans (le_max_left _ _), max Tl Tn, hTn.trans (le_max_right _ _), ?_⟩
  intro q _ hq H hi x hx hroot hsmall
  have hx2 := hTn.trans ((le_max_right Tl Tn).trans hx)
  have hu' := hupper q ((le_max_left Qu R).trans hq) H x (b * x) hx2 hsmall
  have hl' := mul_le_mul_of_nonneg_left (hTl x ((le_max_left Tl Tn).trans hx) q) hh0.le
  rw [hi] at hu'
  have hraw :
    ((h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) - (K.function (1 / 2)).re) *
        Real.sqrt x ≤
      K.mass * subgroupConductorLogSum H + ((h : ℝ) - 1) * (ε / (4 * ((h : ℝ) - 1)) * Real.log q) +
        (h : ℝ) * C * (1 + Real.log q * Real.log x / Real.sqrt x) +
        (h : ℝ) * δ * Real.sqrt x := by
    have hc : 0 ≤ (h : ℝ) * Cl := mul_nonneg hh0.le hCl.le
    dsimp only [C, subgroupConductorLogSum]
    simp only [mul_div_assoc] at hu' hl' ⊢
    nlinarith only [hu', hl', hc]
  have hallow : ((h : ℝ) - 1) * (ε / (4 * ((h : ℝ) - 1)) * Real.log q) = ε * Real.log q / 4 := by
    have hn0 : (h : ℝ) - 1 ≠ 0 := (sub_pos.mpr hhR).ne'
    have hc := div_mul_cancel₀ ε (mul_ne_zero (by norm_num only : (4 : ℝ) ≠ 0) hn0)
    have he := congrArg (fun y : ℝ ↦ y * Real.log q) hc
    nlinarith only [he]
  have hL : 8 * (h : ℝ) * C / (ε * 1) ≤ Real.log q := by
    simpa only [mul_one, Function.comp_apply] using hR q ((le_max_right Qu R).trans hq)
  have herr := hn x ((le_max_right Tl Tn).trans hx) (Real.log q) hL
  have hdelta : (h : ℝ) * δ * Real.sqrt x ≤ ε * Real.log q / 4 := by
    have he := mul_le_mul_of_nonneg_left hroot (mul_nonneg hh0.le hδ.le)
    have hid : (h : ℝ) * δ * d = ε / 4 := by
      have hp : δ * (4 * (h : ℝ) * d) = ε :=
        div_mul_cancel₀ _ (ne_of_gt (mul_pos (mul_pos (by norm_num only) hh0) hd))
      nlinarith only [hp]
    simpa only [← mul_assoc, hid, div_mul_eq_mul_div] using he
  have hqlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  rw [hallow] at hraw
  simp only [mul_one] at herr
  linarith only [hraw, herr, hdelta, mul_nonneg hε.le hqlog]

end MellinKernel

namespace MellinKernel

/-- If an admissible kernel has a positive truncated main coefficient,
GRH bounds the least outside prime by the square of the exact conductor
cost times sqrt b mass / coefficient, plus any positive ambient logarithmic
allowance. The cutoff grows uniformly even for bounded conductors; the
conductor sum upper bound controls its scale. No additional analytic premise
or assumption excluding bounded conductors is used. -/
theorem exists_least_prime_outside_le_conductor_sum (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h : ℕ} (hh : 1 < h) {b ε : ℝ}
    (hb : 0 < b) (hε : 0 < ε)
    (hA : 0 < (h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) - (K.function (1 / 2)).re) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H : Subgroup (ZMod q)ˣ),
              H.index = h →
                ∃ p : ℕ,
                  IsLeast (primesOutside q H) p ∧
                    (p : ℝ) ≤
                      (Real.sqrt b * K.mass /
                              ((h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) -
                                (K.function (1 / 2)).re) *
                            subgroupConductorLogSum H +
                          ε * Real.log q) ^
                        2 := by
  let A := (h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) - (K.function (1 / 2)).re
  let a := Real.sqrt b * K.mass / A
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have ha : 0 < a := div_pos (mul_pos hs (mass_pos K)) hA
  have hhR : (1 : ℝ) < h := by exact_mod_cast hh
  let d := (a * ((h : ℝ) - 1) + ε) / Real.sqrt b
  have hd : 0 < d := div_pos (add_pos (mul_pos ha (sub_pos.mpr hhR)) hε) hs
  let e := (A * ε / Real.sqrt b) / 2
  have he : 0 < e := half_pos (div_pos (mul_pos hA hε) hs)
  obtain ⟨Qc, hQc, T, hT, hc⟩ := exists_conductor_comparison_scale K hg hh hb hd he
  have hlog :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      ((Real.sqrt T * Real.sqrt b + 1) / ε)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hlog
  refine ⟨max Qc R, hQc.trans (le_max_left _ _), ?_⟩
  intro q _ hq H hi
  have hq2 : 2 ≤ q := (by norm_num only : 2 ≤ 20000).trans (hQc.trans ((le_max_left Qc R).trans hq))
  have hL : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
  have hproper : H ≠ ⊤ := by
    intro htop
    have hidx : h = 1 := by rw [← hi, htop, Subgroup.index_top]
    exact (ne_of_gt hh) hidx
  obtain ⟨p, hp⟩ := exists_least_prime_outside H hproper
  refine ⟨p, hp, ?_⟩
  let B := a * subgroupConductorLogSum H + ε * Real.log q
  have hB : 0 < B :=
    add_pos_of_nonneg_of_pos (mul_nonneg ha.le (subgroupConductorLogSum_nonneg H)) (mul_pos hε hL)
  change (p : ℝ) ≤ B ^ 2
  by_contra hn
  have hBp : B ^ 2 < (p : ℝ) := lt_of_not_ge hn
  let x := B ^ 2 / b
  have hx : 0 < x := div_pos (sq_pos_of_pos hB) hb
  have hroot : Real.sqrt x = B / Real.sqrt b := by
    rw [Real.sqrt_div (sq_nonneg B), Real.sqrt_sq hB.le]
  have hlow : Real.sqrt T ≤ B / Real.sqrt b := by
    have hl := (div_le_iff₀ hε).mp (hR q ((le_max_right Qc R).trans hq))
    have hnon := mul_nonneg ha.le (subgroupConductorLogSum_nonneg H)
    apply (le_div_iff₀ hs).mpr
    dsimp only [B]
    simp only [Function.comp_apply] at hl
    linarith only [hl, hnon]
  have hxT : T ≤ x := by
    have hr := mul_self_le_mul_self (Real.sqrt_nonneg T) (hlow.trans_eq hroot.symm)
    nlinarith only [hr, Real.sq_sqrt (zero_le_two.trans hT), Real.sq_sqrt hx.le]
  have hupper : Real.sqrt x ≤ d * Real.log q := by
    have hu := mul_le_mul_of_nonneg_left (subgroupConductorLogSum_le H) ha.le
    rw [hi] at hu
    rw [hroot]
    apply (div_le_iff₀ hs).mpr
    have hid : d * Real.sqrt b = a * ((h : ℝ) - 1) + ε := div_mul_cancel₀ _ hs.ne'
    have hidL := congrArg (fun y : ℝ ↦ y * Real.log q) hid
    dsimp only [B]
    nlinarith only [hu, hidL]
  have hbx : b * x = B ^ 2 := by
    dsimp only [x]
    rw [mul_comm, div_mul_cancel₀ _ hb.ne']
  have hsmall : ∀ r : ℕ, r.Prime → ¬r ∣ q → (r : ℝ) ≤ b * x → residueInSubgroup q H r := by
    intro r hr hnd hle
    by_contra hnr
    have hmin : (p : ℝ) ≤ r := Nat.cast_le.mpr (hp.2 ⟨hr, hnd, hnr⟩)
    rw [hbx] at hle
    exact (not_le_of_gt hBp) (hmin.trans hle)
  have hcomp := hc q ((le_max_left Qc R).trans hq) H hi x hxT hupper hsmall
  have hcoef : A * (a / Real.sqrt b) = K.mass := by
    have hac : a * A = Real.sqrt b * K.mass := div_mul_cancel₀ _ hA.ne'
    rw [← mul_div_assoc, mul_comm A a, hac, mul_div_cancel_left₀ _ hs.ne']
  have hmain :
    A * Real.sqrt x = K.mass * subgroupConductorLogSum H + (A * ε / Real.sqrt b) * Real.log q := by
    rw [hroot]
    calc
      A * (B / Real.sqrt b) =
          (A * (a / Real.sqrt b)) * subgroupConductorLogSum H +
            (A * ε / Real.sqrt b) * Real.log q :=
        by
        dsimp only [B]; ring
      _ = _ := by rw [hcoef]
  have heq : (A * ε / Real.sqrt b) * Real.log q = 2 * (e * Real.log q) := by
    dsimp only [e]
    ring
  rw [heq] at hmain
  change A * Real.sqrt x ≤ K.mass * subgroupConductorLogSum H + e * Real.log q at hcomp
  linarith only [hcomp, hmain, mul_pos he hL]

/-- A strict scalar kernel certificate replaces the exact conductor
coefficient by sqrt c / (h-1). Under GRH, the least outside prime is bounded
by its square with any positive ambient logarithmic allowance. This supplies
the conductor-sum form of a certified kernel bound, without discarding the
primitive conductor information. -/
theorem least_prime_bound_of_conductor_certificate (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h : ℕ} (hh : 1 < h) {b c ε : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hε : 0 < ε)
    (hA : 0 < (h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) - (K.function (1 / 2)).re)
    (hcert :
      b * (((h : ℝ) - 1) * K.mass) ^ 2 <
        c *
          ((h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) - (K.function (1 / 2)).re) ^
            2) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H : Subgroup (ZMod q)ˣ),
              H.index = h →
                ∃ p : ℕ,
                  IsLeast (primesOutside q H) p ∧
                    (p : ℝ) ≤
                      (Real.sqrt c / ((h : ℝ) - 1) * subgroupConductorLogSum H + ε * Real.log q) ^
                        2 := by
  let A := (h : ℝ) * (∫ u in 0..b, (K.transform u).re / Real.sqrt u) - (K.function (1 / 2)).re
  have hhR : (1 : ℝ) < h := by exact_mod_cast hh
  have hleft : 0 ≤ Real.sqrt b * (((h : ℝ) - 1) * K.mass) :=
    mul_nonneg (Real.sqrt_nonneg b) (mul_nonneg (sub_pos.mpr hhR).le (mass_pos K).le)
  have hright : 0 < Real.sqrt c * A := mul_pos (Real.sqrt_pos.mpr hc) hA
  have hsleft :
    (Real.sqrt b * (((h : ℝ) - 1) * K.mass)) ^ 2 = b * (((h : ℝ) - 1) * K.mass) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb.le]
  have hsright : (Real.sqrt c * A) ^ 2 = c * A ^ 2 := by rw [mul_pow, Real.sq_sqrt hc.le]
  have hmul : Real.sqrt b * (((h : ℝ) - 1) * K.mass) ≤ Real.sqrt c * A := by
    nlinarith only [hsleft, hsright, hcert, hleft, hright]
  have hratio : Real.sqrt b * K.mass / A ≤ Real.sqrt c / ((h : ℝ) - 1) := by
    apply (div_le_div_iff₀ hA (sub_pos.mpr hhR)).mpr
    nlinarith only [hmul]
  obtain ⟨Q, hQ, hbnd⟩ := exists_least_prime_outside_le_conductor_sum K hg hh hb hε hA
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H hi
  obtain ⟨p, hp, hpbound⟩ := hbnd q hq H hi
  refine ⟨p, hp, hpbound.trans ?_⟩
  have hbase : 0 ≤ Real.sqrt b * K.mass / A * subgroupConductorLogSum H + ε * Real.log q :=
    add_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg b) (mass_pos K).le) hA.le)
        (subgroupConductorLogSum_nonneg H))
      (mul_nonneg hε.le (Real.log_natCast_nonneg q))
  have hcompare :=
    add_le_add (mul_le_mul_of_nonneg_right hratio (subgroupConductorLogSum_nonneg H))
      (le_refl (ε * Real.log q))
  simpa only [← pow_two] using mul_self_le_mul_self hbase hcompare

end MellinKernel

end PseudoPrime.LLS.PaperStatements
