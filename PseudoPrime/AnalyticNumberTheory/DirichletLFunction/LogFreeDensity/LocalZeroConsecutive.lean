/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.PowerSumContourSelector
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroLogCutoff

/-! # Consecutive local zero moments with linear order envelopes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- For an actual primitive near-one zero and a natural upper bound `N` for its
explicit local multiplicity ceiling, select a local reciprocal moment at order
`3N+1` through `4N` with lower bound `(3η)^(-m)/(8 * 160^N)`. Retain the actual
support and analytic multiplicities, expand them into repeated nodes, and apply
the zero-padded consecutive power-sum estimate. This replaces the product of
block scale and multiplicity by an order linear in the shared count cap. -/
theorem exists_completedLFunction_local_consecutive_moment_of_cap {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) {c ρ : ℂ} (hcre : c.re = 1 + η)
    (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η) (hzero : χ.completedLFunction ρ = 0)
    (hc : χ.completedLFunction c ≠ 0) (N : ℕ)
    (hcap :
      Nat.ceil
          (completedZeroLocalLogBoundConstant * (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ≤
        N) :
    ∃ j ∈ Finset.range N,
      (1 / (8 * (160 : ℝ) ^ N)) * (1 / (3 * η)) ^ (3 * N + 1 + j) ≤
        ‖completedLFunctionLocalReciprocalMoment χ hχ c η (3 * N + 1 + j)‖ := by
  classical
  obtain ⟨_, _, _, _, C, _, _, _, _, _, hmass, hblock, _, hCeq⟩ :=
    exists_completedLFunction_local_zero_block_with_remote_tail_matching_scale hq hχ hp hinv hη
      hηsmall 2 (le_refl 2) hcre hcim hρre hzero hc
  obtain ⟨s, hs, hρs, _⟩ := hblock
  let S := (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset
  let d := MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|)
  let mult := fun v : ℂ ↦ (d v).toNat
  let node := fun v : ℂ ↦ (c - v)⁻¹
  have hF : AnalyticOnNhd ℂ χ.completedLFunction (Metric.ball c |80 * η|) := fun v hv ↦
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt v
  have hnonneg : ∀ v, 0 ≤ d v := fun v ↦ MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF v
  have hρdiv : d ρ ≠ 0 := (hs ρ).mp hρs
  have hρS : ρ ∈ S := (Set.Finite.mem_toFinset _).mpr hρdiv
  have hρpos : 0 < d ρ := lt_of_le_of_ne (hnonneg ρ) (Ne.symm hρdiv)
  have hmult : 0 < mult ρ := by
    have hcast := Int.toNat_of_nonneg (hnonneg ρ)
    exact_mod_cast hcast.symm ▸ hρpos
  have hmassNat : (∑ v ∈ S, mult v) ≤ C := by exact_mod_cast hmass
  have hcap' : (∑ v ∈ S, mult v) ≤ N := by
    rw [hCeq] at hmassNat
    exact hmassNat.trans hcap
  have hρneq : c - ρ ≠ 0 := by
    intro heq
    apply hc
    rw [sub_eq_zero.mp heq]
    exact hzero
  have hreal : |c.re - ρ.re| ≤ 2 * η := by
    rw [hcre]
    obtain ⟨hlo, hhi⟩ := abs_le.mp hρre
    exact abs_le.mpr ⟨by linarith only [hhi, hη], by linarith only [hlo, hη]⟩
  have hdist : ‖c - ρ‖ ≤ 3 * η := by
    have h := Complex.norm_le_abs_re_add_abs_im (c - ρ)
    rw [Complex.sub_re, Complex.sub_im, hcim, sub_self, abs_zero, add_zero] at h
    exact h.trans (hreal.trans (by linarith only [hη]))
  have hnear : 1 / (3 * η) ≤ ‖node ρ‖ := by
    rw [show node ρ = (c - ρ)⁻¹ by rfl, norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le (norm_pos_iff.mpr hρneq) hdist
  obtain ⟨j, hj, hbound⟩ :=
    exists_finset_weighted_power_sum_norm_ge_consecutive_triple_block_of_cap S mult node N hcap' ρ
      hρS hmult (1 / (3 * η)) (one_div_pos.mpr (mul_pos (by norm_num only) hη)) hnear
  refine ⟨j, hj, ?_⟩
  have hcast : ∀ v ∈ S, (mult v : ℂ) = (d v : ℂ) := by
    intro v hv
    exact_mod_cast Int.toNat_of_nonneg (hnonneg v)
  have heq :
    (∑ v ∈ S, (mult v : ℂ) * node v ^ (3 * N + 1 + j)) =
      completedLFunctionLocalReciprocalMoment χ hχ c η (3 * N + 1 + j) := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [hcast v hv]
  rw [heq] at hbound
  exact hbound

/-- Above count cap four, the rapidly decaying geometric factor absorbs the
linear mass prefactor. Prove the base case numerically and monotonicity by induction.
This supplies a coarse absolute budget for the remote tail in a linear-order block. -/
theorem scaled_geometric_mass_le_one (N : ℕ) (hN : 4 ≤ N) :
    102400 * (N : ℝ) * (1 / 64 : ℝ) ^ N ≤ 1 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num only
  | succ n hn ih =>
    have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hfactor : ((n : ℝ) + 1) / 64 ≤ n := by linarith only [hnreal]
    calc
      _ = (102400 * (((n : ℝ) + 1) / 64)) * (1 / 64 : ℝ) ^ n := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      _ ≤ 102400 * (n : ℝ) * (1 / 64 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor (by norm_num only))
          (pow_nonneg (by norm_num only) n)
      _ ≤ 1 := ih

/-- At every power at least three times a count cap of at least four, combine
the selector coefficient loss with the remote-radius ratio and mass prefactor.
The product is at most one. This keeps remote absorption exponential in the cap
rather than requiring a cap times a separate block threshold. -/
theorem consecutive_block_remote_geometric_budget (N m : ℕ) (hN : 4 ≤ N) (hm : 3 * N ≤ m) :
    (102400 * (N : ℝ)) * ((160 : ℝ) ^ N * (3 / 80 : ℝ) ^ m) ≤ 1 := by
  have hpow : (3 / 80 : ℝ) ^ m ≤ (3 / 80 : ℝ) ^ (3 * N) :=
    pow_le_pow_of_le_one (by norm_num only) (by norm_num only) hm
  have hcombine : (160 : ℝ) ^ N * (3 / 80 : ℝ) ^ (3 * N) = ((160 : ℝ) * (3 / 80 : ℝ) ^ 3) ^ N := by
    rw [pow_mul, ← mul_pow]
  have hbase : (160 : ℝ) * (3 / 80 : ℝ) ^ 3 ≤ 1 / 64 := by norm_num only
  have hsmall :=
    (mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num only) N)).trans
      (hcombine.le.trans (pow_le_pow_left₀ (by norm_num only) hbase N))
  exact
    (mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num only) (Nat.cast_nonneg N))).trans
      (scaled_geometric_mass_le_one N hN)

/-- For a nonzero positive-order scale, factorial-free normalization of the
remote-radius power leaves the scaled inverse-square mass divided by `80^(m-2)`.
Factor the two base powers and cancel the scale. This isolates the dimensionless mass. -/
theorem normalized_remote_radius_power (η M : ℝ) (m : ℕ) (hη : η ≠ 0) (hm : 2 ≤ m) :
    η ^ m * ((80 * η)⁻¹ ^ (m - 2) * M) = (η ^ 2 * M) / (80 : ℝ) ^ (m - 2) := by
  have hscale : η * (80 * η)⁻¹ = (1 / 80 : ℝ) := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hη, one_mul]
    exact (one_div (80 : ℝ)).symm
  calc
    _ = (η ^ 2 * M) * (η * (80 * η)⁻¹) ^ (m - 2) := by
      conv_lhs =>
        arg 1
        rw [← Nat.sub_add_cancel hm, pow_add]
      rw [mul_pow]
      ring
    _ = _ := by
      rw [hscale, div_pow, one_pow]; ring

/-- For a cap at least four and power at least three times the cap, the normalized
remote mass is at most half the consecutive local signal. Apply the geometric
budget and clear a positive denominator. This is the scalar remote absorption step. -/
theorem normalized_remote_mass_budget (N m : ℕ) (hN : 4 ≤ N) (hm : 3 * N ≤ m) :
    (N : ℝ) / (80 : ℝ) ^ (m - 2) ≤ 1 / (16 * (160 : ℝ) ^ N * (3 : ℝ) ^ m) := by
  have hmTwo : 2 ≤ m := (by norm_num only : 2 ≤ 3 * 4).trans ((Nat.mul_le_mul_left 3 hN).trans hm)
  have h80 : (80 : ℝ) ^ m = (80 : ℝ) ^ (m - 2) * 6400 := by
    conv_lhs => rw [← Nat.sub_add_cancel hmTwo, pow_add]
    norm_num only
  have hsmall := consecutive_block_remote_geometric_budget N m hN hm
  apply
    (le_div_iff₀
        (mul_pos (mul_pos (by norm_num only) (pow_pos (by norm_num only) _))
          (pow_pos (by norm_num only) _))).mpr
  convert hsmall using 1
  rw [div_pow, h80]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num only
  ring

/-- For conductor, scale, and height, define the dimensionless inverse-square mass
majorant by multiplying the fixed completed-genus mass bound by `η^2`.
The formula retains the conductor-height dependence. A natural upper bound for this
quantity can be shared with the local multiplicity cap in a linear-order detector. -/
noncomputable def completedGenusScaledMassUpperBound (q : ℕ) (η t : ℝ) : ℝ :=
  η ^ 2 *
    ((1 / η) *
      (4 / η + completedGenusMassShiftConstant * (Real.log (4 + |t|) + 1) + Real.log q + 4 +
        completedGenusMassCenterConstant * (Real.log 4 + 1)))

/-- For a primitive nonprincipal character and a right-of-one center, if the
explicit dimensionless mass majorant is at most `N ≥ 4`, every remote moment at
order at least `3N` is below half the consecutive local signal after normalization.
Use the actual radius `80η`, the unconditional inverse-square mass bound, and the
geometric budget. No bounded scaled conductor-height assumption is used. -/
theorem normalized_completed_remote_moment_le_linear_cap {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2) {c : ℂ} (t : ℝ) (hcre : c.re = 1 + η) (hcim : c.im = t)
    (N m : ℕ) (hN : 4 ≤ N) (hm : 3 * N ≤ m) (hcap : completedGenusScaledMassUpperBound q η t ≤ N) :
    η ^ m * ‖completedLFunctionRemoteReciprocalMoment χ c η m‖ ≤
      1 / (16 * (160 : ℝ) ^ N * (3 : ℝ) ^ m) := by
  classical
  have hcRight : 1 < c.re := by
    rw [hcre]; linarith only [hη]
  have hcenter : c = ((1 + η : ℝ) : ℂ) + Complex.I * t := by
    apply Complex.ext
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hcre
    · simpa only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, zero_add, one_mul] using hcim
  obtain ⟨A, B, hA, hB, _, _, hglobal⟩ :=
    exists_completed_genus_inverse_square_mass_le_uniform_bound hq hχ hp hinv hη hηsmall t
  let M :=
    (1 / η) *
      (4 / η + completedGenusMassShiftConstant * (Real.log (4 + |t|) + 1) + Real.log q + 4 +
        completedGenusMassCenterConstant * (Real.log 4 + 1))
  have hglobal' :
    ∑' v : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℝ) * ‖(c - v)⁻¹‖ ^ 2 ≤
      M := by
    simpa only [M, hcenter, hA, hB] using hglobal
  let S : Set ℂ := {v | 80 * η ≤ ‖c - v‖}
  have hsubset :=
    (completed_genus_inverse_square_subset_mass_le hq hχ hp hinv S hcRight).trans hglobal'
  have hremote : ∀ v ∈ S, 8 * (10 * η) ≤ ‖c - v‖ := by
    intro v hv
    simpa only [S, Set.mem_ofPred_eq, show (8 : ℝ) * (10 * η) = 80 * η by ring] using hv
  have hmTwo : 2 ≤ m := (by norm_num only : 2 ≤ 3 * 4).trans ((Nat.mul_le_mul_left 3 hN).trans hm)
  have htail :=
    (norm_tsum_completed_genus_remote_reciprocal_power_le hq hχ hp hinv S hcRight
        (mul_pos (by norm_num only : (0 : ℝ) < 10) hη) hremote m hmTwo).2
  have htail' : ‖completedLFunctionRemoteReciprocalMoment χ c η m‖ ≤ (80 * η)⁻¹ ^ (m - 2) * M := by
    have hpow : 0 ≤ (8 * (10 * η))⁻¹ ^ (m - 2) :=
      pow_nonneg
        (inv_nonneg.mpr (mul_nonneg (by norm_num only) (mul_nonneg (by norm_num only) hη.le)))
        (m - 2)
    have h := htail.trans (mul_le_mul_of_nonneg_left hsubset hpow)
    simpa only [completedLFunctionRemoteReciprocalMoment, S, Set.mem_ofPred_eq,
      show (8 : ℝ) * (10 * η) = 80 * η by ring] using h
  have hscaled := mul_le_mul_of_nonneg_left htail' (pow_nonneg hη.le m)
  rw [normalized_remote_radius_power η M m (ne_of_gt hη) hmTwo] at hscaled
  exact
    (hscaled.trans (div_le_div_of_nonneg_right hcap (pow_nonneg (by norm_num only) _))).trans
      (normalized_remote_mass_budget N m hN hm)

/-- For nonzero scale, normalize the consecutive local reciprocal-power lower
bound to `1/(8 * 160^N * 3^m)`. Reuse factorial cancellation at order zero and
combine denominators. This aligns the local and remote signals. -/
theorem normalized_local_consecutive_signal (η : ℝ) (N m : ℕ) (hη : η ≠ 0) :
    η ^ m * ((1 / (8 * (160 : ℝ) ^ N)) * (1 / (3 * η)) ^ m) =
      1 / (8 * (160 : ℝ) ^ N * (3 : ℝ) ^ m) := by
  have h := factorial_normalized_reciprocal_signal η (1 / (8 * (160 : ℝ) ^ N)) 0 m hη
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, mul_one] at h
  rw [h, div_pow, one_pow, div_mul_div_comm, one_mul]

/-- For an actual primitive near-one zero, a shared natural cap at least four
controlling both the explicit local multiplicity ceiling and dimensionless genus
mass gives a completed logarithmic-derivative detector with `3N ≤ n < 4N` and
normalized signal at least `1/(16 * 160^N * 3^(n+1))`. Combine the consecutive
local moment with the radius-sensitive remote estimate and the exact derivative
factorization. This removes the product order loss from the general-scale detector. -/
theorem exists_completedLFunction_linear_order_detector_of_cap {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) {c ρ : ℂ} (hcre : c.re = 1 + η)
    (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η) (hzero : χ.completedLFunction ρ = 0)
    (hc : χ.completedLFunction c ≠ 0) (N : ℕ) (hN : 4 ≤ N)
    (hlocalcap :
      Nat.ceil
          (completedZeroLocalLogBoundConstant * (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ≤
        N)
    (hmasscap : completedGenusScaledMassUpperBound q η ρ.im ≤ N) :
    ∃ n : ℕ,
      3 * N ≤ n ∧
        n + 1 ≤ 4 * N ∧
        1 / (16 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1)) ≤
          (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖iteratedDeriv n (fun z : ℂ ↦ logDeriv χ.completedLFunction z) c‖ := by
  obtain ⟨j, hj, hlocal⟩ :=
    exists_completedLFunction_local_consecutive_moment_of_cap hq hχ hp hinv hη hηsmall hcre hcim
      hρre hzero hc N hlocalcap
  let n := 3 * N + j
  have hnm : n + 1 = 3 * N + 1 + j := by
    dsimp only [n]; ring
  have hnlow : 3 * N ≤ n := Nat.le_add_right _ _
  have hnupper : n + 1 ≤ 4 * N := by
    have hjle := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    calc
      n + 1 = 3 * N + (j + 1) := by
        dsimp only [n]; ring
      _ ≤ 3 * N + N := Nat.add_le_add_left hjle _
      _ = _ := by ring
  have hnpos : 0 < n :=
    (lt_of_lt_of_le (by norm_num only : 0 < 3 * 4) (Nat.mul_le_mul_left 3 hN)).trans_le hnlow
  have hm : 3 * N ≤ n + 1 := hnlow.trans (Nat.le_succ n)
  rw [← hnm] at hlocal
  have hlocal' := mul_le_mul_of_nonneg_left hlocal (pow_nonneg hη.le (n + 1))
  rw [normalized_local_consecutive_signal η N (n + 1) (ne_of_gt hη)] at hlocal'
  have hremote :=
    normalized_completed_remote_moment_le_linear_cap hq hχ hp hinv hη (by linarith only [hηsmall])
      ρ.im hcre hcim N (n + 1) hN hm hmasscap
  let L := completedLFunctionLocalReciprocalMoment χ hχ c η (n + 1)
  let R := completedLFunctionRemoteReciprocalMoment χ c η (n + 1)
  have htriangle : ‖L‖ ≤ ‖L + R‖ + ‖R‖ := by
    have h := norm_sub_le (L + R) R
    simpa only [add_sub_cancel_right] using h
  have htriangle' := mul_le_mul_of_nonneg_left htriangle (pow_nonneg hη.le (n + 1))
  have hsignal :
    1 / (8 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1)) =
      2 * (1 / (16 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1))) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num only
    ring
  rw [hsignal] at hlocal'
  have hcombined : 1 / (16 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1)) ≤ η ^ (n + 1) * ‖L + R‖ := by
    change _ ≤ η ^ (n + 1) * ‖L‖ at hlocal'
    change η ^ (n + 1) * ‖R‖ ≤ _ at hremote
    linarith only [hlocal', hremote, htriangle']
  have hcRight : 1 < c.re := by
    rw [hcre]; linarith only [hη]
  have hnorm :=
    norm_completedLFunction_logDeriv_eq_local_remote_moment hq hχ hp hinv hη hcRight n hnpos
  rw [completedLFunction_logDeriv_iteratedDerivWithin_eq hχ hcRight hc n] at hnorm
  refine ⟨n, hnlow, hnupper, ?_⟩
  rw [hnorm, ← mul_assoc, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
  exact hcombined

/-- When the scaled gamma majorant is at most a count cap `N ≥ 4`, every order
at least `3N` absorbs the gamma correction into half the linear-cap signal.
Compare its geometric ratio with the radius-sensitive remote-tail budget.
This preserves a linear order envelope when transferring to the ordinary L-function. -/
theorem normalized_gamma_le_linear_cap_signal (η G H : ℝ) (N n : ℕ) (hη : 0 ≤ η)
    (hηsmall : 12 * η ≤ 3 / 80) (hcap : η * G * H ≤ N) (hN : 4 ≤ N) (hn : 3 * N ≤ n) :
    η * G * H * (4 * η) ^ n ≤ 1 / (32 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1)) := by
  have hpow :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by norm_num only) hη) hηsmall n)
      (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 160) N)
  have hcoef : 96 * (N : ℝ) ≤ 102400 * N :=
    mul_le_mul_of_nonneg_right (by norm_num only) (Nat.cast_nonneg N)
  have hsmall : (96 * (N : ℝ)) * ((160 : ℝ) ^ N * (12 * η) ^ n) ≤ 1 :=
    (mul_le_mul hcoef hpow
          (mul_nonneg (pow_nonneg (by norm_num only) N)
            (pow_nonneg (mul_nonneg (by norm_num only) hη) n))
          (mul_nonneg (by norm_num only) (Nat.cast_nonneg N))).trans
      (consecutive_block_remote_geometric_budget N n hN hn)
  apply
    (le_div_iff₀
        (mul_pos (mul_pos (by norm_num only) (pow_pos (by norm_num only) _))
          (pow_pos (by norm_num only) _))).mpr
  have hdenom : 0 ≤ 32 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1) :=
    mul_nonneg (mul_nonneg (by norm_num only) (pow_nonneg (by norm_num only) N))
      (pow_nonneg (by norm_num only) (n + 1))
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcap
        (pow_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hη) n))
      hdenom
  apply hscaled.trans
  convert hsmall using 1
  simp only [pow_succ, mul_pow]
  rw [show (12 : ℝ) ^ n = (3 : ℝ) ^ n * (4 : ℝ) ^ n by
      rw [← mul_pow]; norm_num only]
  ring

/-- One absolute gamma constant works for every primitive near-one zero: a shared
natural cap controlling local multiplicity, dimensionless genus mass, and scaled
gamma growth yields an ordinary logarithmic-derivative detector with `3N ≤ n < 4N`
and normalized signal at least `1/(32 * 160^N * 3^(n+1))`. Apply the completed
linear-order detector and subtract the normalized gamma correction. The remaining
cap conditions are explicit numerical bounds, with no unproved analytic input. -/
theorem exists_ordinary_LFunction_linear_order_detector_of_cap :
    ∃ G : ℝ,
      0 ≤ G ∧
        ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
          2 ≤ q →
            χ ≠ 1 →
            χ.IsPrimitive →
            χ⁻¹ ≠ 1 →
            ∀ {η : ℝ},
              0 < η →
                η ≤ 1 / 1288 →
                ∀ {c ρ : ℂ},
                  c.re = 1 + η →
                    c.im = ρ.im →
                    |ρ.re - 1| ≤ η →
                    χ.completedLFunction ρ = 0 →
                    χ.completedLFunction c ≠ 0 →
                    ∀ N : ℕ,
                      4 ≤ N →
                        Nat.ceil
                            (completedZeroLocalLogBoundConstant *
                              (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ≤
                          N →
                        completedGenusScaledMassUpperBound q η ρ.im ≤ N →
                        η * G * (Real.log (4 * |ρ.im| + 4) + 1) ≤ N →
                        ∃ n : ℕ,
                          3 * N ≤ n ∧
                            n + 1 ≤ 4 * N ∧
                            1 / (32 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1)) ≤
                              (η ^ (n + 1) / (n.factorial : ℝ)) *
                                ‖iteratedDeriv n (fun z : ℂ ↦ logDeriv χ.LFunction z) c‖ := by
  obtain ⟨G, hG, hgamma⟩ := exists_uniform_gamma_subtraction_for_ordinary_LFunction_derivative_all
  refine ⟨G, hG, ?_⟩
  intro q _ χ hq hχ hp hinv η hη hηsmall c ρ hcre hcim hρre hzero hc N hN hlocalcap hmasscap
    hgammacap
  obtain ⟨n, hnlow, hnupper, hcompleted⟩ :=
    exists_completedLFunction_linear_order_detector_of_cap hq hχ hp hinv hη hηsmall hcre hcim hρre
      hzero hc N hN hlocalcap hmasscap
  have hbudget :=
    normalized_gamma_le_linear_cap_signal η G (Real.log (4 * |ρ.im| + 4) + 1) N n hη.le
      (by linarith only [hηsmall]) hgammacap hN hnlow
  have hcRight : 1 < c.re := by
    rw [hcre]; linarith only [hη]
  have hcHi : c.re ≤ 5 / 4 := by
    rw [hcre]; linarith only [hηsmall]
  have hordinary :=
    hgamma n hχ hcRight hcRight.le hcHi (abs_nonneg ρ.im) (by rw [hcim]) (A :=
      ‖iteratedDeriv n (logDeriv χ.completedLFunction) c‖) (le_refl _)
  have hscaled :=
    mul_le_mul_of_nonneg_left hordinary
      (div_nonneg (pow_nonneg hη.le (n + 1)) (Nat.cast_nonneg n.factorial))
  rw [mul_sub, factorial_normalized_gamma_correction] at hscaled
  have hsignal :
    1 / (16 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1)) =
      2 * (1 / (32 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1))) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num only
    ring
  rw [hsignal] at hcompleted
  refine ⟨n, hnlow, hnupper, ?_⟩
  change _ ≤ (η ^ (n + 1) / (n.factorial : ℝ)) * ‖iteratedDeriv n (logDeriv χ.LFunction) c‖
  linarith only [hcompleted, hbudget, hscaled]

/-- The fixed shifted genus-mass constant is positive by its defining uniform
logarithmic-derivative bound. This permits scaling conductor-height comparisons. -/
theorem completedGenusMassShiftConstant_pos : 0 < completedGenusMassShiftConstant :=
  (Classical.choose_spec exists_uniform_norm_completed_logDeriv_small_shift_bound).1

/-- The fixed center genus-mass constant is positive by its defining center bound.
This permits scaling the dimensionless mass estimate. -/
theorem completedGenusMassCenterConstant_pos : 0 < completedGenusMassCenterConstant :=
  (Classical.choose_spec
      (exists_norm_completed_logDeriv_small_shift_bound (r := 1) (by norm_num only)
        (by norm_num only))).1

/-- For conductor at least two, compare the conductor, local height, and gamma
height logarithms with `log(q(|t|+3))`. Use positive-argument monotonicity and the
factor-four logarithm identity. This aligns all detector budgets to one scale. -/
theorem conductor_height_log_comparisons (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    0 ≤ Real.log ((q : ℝ) * (|t| + 3)) ∧
      Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 3)) ∧
      Real.log (4 + |t|) ≤ Real.log ((q : ℝ) * (|t| + 3)) ∧
      Real.log (4 * |t| + 4) ≤ Real.log 4 + Real.log ((q : ℝ) * (|t| + 3)) := by
  have hqreal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num only) hqreal
  have ht : 0 ≤ |t| := abs_nonneg t
  have hqX : (q : ℝ) ≤ (q : ℝ) * (|t| + 3) :=
    le_mul_of_one_le_right hqpos.le (by linarith only [ht])
  have hfourX : 4 + |t| ≤ (q : ℝ) * (|t| + 3) := by
    have h := mul_le_mul_of_nonneg_right hqreal (by linarith only [ht] : 0 ≤ |t| + 3)
    linarith only [h, ht]
  have hXpos : (0 : ℝ) < (q : ℝ) * (|t| + 3) := mul_pos hqpos (by linarith only [ht])
  refine
    ⟨Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 2).trans (hqreal.trans hqX)),
      Real.log_le_log hqpos hqX, Real.log_le_log (by linarith only [ht]) hfourX, ?_⟩
  have harg : 4 * |t| + 4 ≤ 4 * ((q : ℝ) * (|t| + 3)) := by
    have h := mul_le_mul_of_nonneg_left hfourX (by norm_num only : (0 : ℝ) ≤ 4)
    linarith only [h]
  have h := Real.log_le_log (by linarith only [ht] : 0 < 4 * |t| + 4) harg
  rwa [Real.log_mul (by norm_num only) (ne_of_gt hXpos)] at h

/-- For positive shift at most one, the explicit dimensionless genus mass is
bounded by an absolute affine function of `η log(q(|t|+3))`. Cancel the shift and
compare the height logarithms. This makes the remote-tail count cap linear in the
same scale as the local multiplicity cap. -/
theorem completedGenusScaledMassUpperBound_le_affine (q : ℕ) (hq : 2 ≤ q) (η t : ℝ) (hη : 0 < η)
    (hηone : η ≤ 1) :
    completedGenusScaledMassUpperBound q η t ≤
      8 + completedGenusMassShiftConstant + completedGenusMassCenterConstant * (Real.log 4 + 1) +
        (completedGenusMassShiftConstant + 1) * (η * Real.log ((q : ℝ) * (|t| + 3))) := by
  obtain ⟨_, hqlog, htlog, _⟩ := conductor_height_log_comparisons q hq t
  have hqscale := mul_le_mul_of_nonneg_left hqlog hη.le
  have htscale := mul_le_mul_of_nonneg_left htlog hη.le
  have hA :=
    mul_le_mul_of_nonneg_left (add_le_add htscale hηone) completedGenusMassShiftConstant_pos.le
  have hlog4 : 0 ≤ Real.log 4 + 1 := add_nonneg (Real.log_nonneg (by norm_num only)) zero_le_one
  have hB :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hηone hlog4)
      completedGenusMassCenterConstant_pos.le
  have hcancel : η ^ 2 * (1 / η) = η := by
    rw [pow_two, one_div, mul_assoc, mul_inv_cancel₀ (ne_of_gt hη), mul_one]
  have hfour : η * (4 / η) = 4 := by
    calc
      _ = 4 * (η * η⁻¹) := by
        rw [div_eq_mul_inv]; ring
      _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hη), mul_one]
  rw [completedGenusScaledMassUpperBound, ← mul_assoc, hcancel]
  have hidentity :
    η *
        (4 / η + completedGenusMassShiftConstant * (Real.log (4 + |t|) + 1) + Real.log q + 4 +
          completedGenusMassCenterConstant * (Real.log 4 + 1)) =
      η * (4 / η) + completedGenusMassShiftConstant * (η * Real.log (4 + |t|) + η) +
        η * Real.log q +
        4 * η +
        completedGenusMassCenterConstant * (η * (Real.log 4 + 1)) := by
    ring
  rw [hidentity, hfour]
  nlinarith only [hA, hB, hqscale, hηone]

/-- For a nonnegative gamma constant and shift at most one, the scaled gamma
height factor is at most an absolute coefficient times `1+η log(q(|t|+3))`.
Compare the gamma height logarithm with the conductor-height logarithm.
This supplies the third numerical budget for the linear-order detector. -/
theorem scaled_gamma_growth_le_linear_scale (q : ℕ) (hq : 2 ≤ q) (η t G : ℝ) (hη : 0 ≤ η)
    (hηone : η ≤ 1) (hG : 0 ≤ G) :
    η * G * (Real.log (4 * |t| + 4) + 1) ≤
      (G * (Real.log 4 + 2)) * (1 + η * Real.log ((q : ℝ) * (|t| + 3))) := by
  obtain ⟨hXlog, _, _, hlog⟩ := conductor_height_log_comparisons q hq t
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
  have hscale := mul_le_mul_of_nonneg_left (add_le_add_right hlog 1) hη
  have hconst := mul_le_mul_of_nonneg_right hηone (add_nonneg hlog4 zero_le_one)
  have hproduct := mul_nonneg (add_nonneg hlog4 zero_le_one) (mul_nonneg hη hXlog)
  have hbound :
    η * (Real.log (4 * |t| + 4) + 1) ≤
      (Real.log 4 + 2) * (1 + η * Real.log ((q : ℝ) * (|t| + 3))) := by
    nlinarith only [hscale, hconst, hproduct]
  have h := mul_le_mul_of_nonneg_left hbound hG
  simpa only [mul_assoc, mul_comm η G, mul_left_comm] using h

/-- For a gamma constant, combine the absolute local-multiplicity, scaled-mass,
and gamma-growth coefficients with the minimum cap four. Multiplying this
coefficient by `1+η log(q(|t|+3))` and taking a ceiling yields one shared natural
cap. This discharges all numerical inputs of the linear-order detector. -/
noncomputable def linearOrderDetectorCapCoefficient (G : ℝ) : ℝ :=
  4 + 644 * completedZeroLocalLogBoundConstant +
    (9 + 2 * completedGenusMassShiftConstant +
      completedGenusMassCenterConstant * (Real.log 4 + 1)) +
    G * (Real.log 4 + 2)

/-- For conductor at least two, positive shift at most one, and nonnegative gamma
constant, the explicit ceiling cap dominates four, local multiplicity, scaled
genus mass, and scaled gamma growth. Its size is bounded linearly by the same
conductor-height scale. Apply the three budget comparisons and ceiling bounds.
This removes the numerical cap assumptions from the actual zero detector. -/
theorem linear_order_detector_numeric_caps (q : ℕ) (hq : 2 ≤ q) (η t G : ℝ) (hη : 0 < η)
    (hηone : η ≤ 1) (hG : 0 ≤ G) :
    let D := linearOrderDetectorCapCoefficient G
    let L := 1 + η * Real.log ((q : ℝ) * (|t| + 3))
    let N := Nat.ceil (D * L)
    4 ≤ N ∧
      Nat.ceil
          (completedZeroLocalLogBoundConstant * (1 + 644 * η * Real.log ((q : ℝ) * (|t| + 3)))) ≤
        N ∧
      completedGenusScaledMassUpperBound q η t ≤ N ∧
      η * G * (Real.log (4 * |t| + 4) + 1) ≤ N ∧ (N : ℝ) ≤ (D + 1) * L := by
  dsimp only
  let S := η * Real.log ((q : ℝ) * (|t| + 3))
  let D := linearOrderDetectorCapCoefficient G
  let B :=
    9 + 2 * completedGenusMassShiftConstant + completedGenusMassCenterConstant * (Real.log 4 + 1)
  have hS : 0 ≤ S := mul_nonneg hη.le (conductor_height_log_comparisons q hq t).1
  have hL : 1 ≤ 1 + S := le_add_of_nonneg_right hS
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
  have hBterm : 0 ≤ completedGenusMassCenterConstant * (Real.log 4 + 1) :=
    mul_nonneg completedGenusMassCenterConstant_pos.le (add_nonneg hlog4 zero_le_one)
  have hGterm : 0 ≤ G * (Real.log 4 + 2) := mul_nonneg hG (add_nonneg hlog4 (by norm_num only))
  have hDfour : 4 ≤ D := by
    dsimp only [D, linearOrderDetectorCapCoefficient]
    linarith only [completedZeroLocalLogBoundConstant_pos, completedGenusMassShiftConstant_pos,
      hBterm, hGterm]
  have hDC : 644 * completedZeroLocalLogBoundConstant ≤ D := by
    dsimp only [D, linearOrderDetectorCapCoefficient]
    linarith only [completedGenusMassShiftConstant_pos, hBterm, hGterm]
  have hDB : B ≤ D := by
    dsimp only [D, B, linearOrderDetectorCapCoefficient]
    linarith only [completedZeroLocalLogBoundConstant_pos, hGterm]
  have hDG : G * (Real.log 4 + 2) ≤ D := by
    dsimp only [D, linearOrderDetectorCapCoefficient]
    linarith only [completedZeroLocalLogBoundConstant_pos, completedGenusMassShiftConstant_pos,
      hBterm]
  have hD : 0 ≤ D := (by norm_num only : (0 : ℝ) ≤ 4).trans hDfour
  have hceil := Nat.le_ceil (D * (1 + S))
  have hNfour : 4 ≤ Nat.ceil (D * (1 + S)) := by
    have hfour : (4 : ℝ) ≤ (Nat.ceil (D * (1 + S)) : ℝ) :=
      (hDfour.trans (le_mul_of_one_le_right hD hL)).trans hceil
    exact_mod_cast hfour
  have hlocal : completedZeroLocalLogBoundConstant * (1 + 644 * S) ≤ D * (1 + S) := by
    have h := mul_le_mul_of_nonneg_right hDC (add_nonneg zero_le_one hS)
    nlinarith only [h, completedZeroLocalLogBoundConstant_pos]
  have haff := completedGenusScaledMassUpperBound_le_affine q hq η t hη hηone
  have hmasslinear : completedGenusScaledMassUpperBound q η t ≤ B * (1 + S) := by
    have hprod :
      0 ≤
        (8 + completedGenusMassShiftConstant +
            completedGenusMassCenterConstant * (Real.log 4 + 1)) *
          S :=
      mul_nonneg
        (add_nonneg (add_nonneg (by norm_num only) completedGenusMassShiftConstant_pos.le) hBterm)
        hS
    dsimp only [B]
    change
      _ ≤
        8 + completedGenusMassShiftConstant + completedGenusMassCenterConstant * (Real.log 4 + 1) +
          (completedGenusMassShiftConstant + 1) * S at haff
    nlinarith only [haff, hprod, completedGenusMassShiftConstant_pos]
  have hmass :=
    hmasslinear.trans ((mul_le_mul_of_nonneg_right hDB (add_nonneg zero_le_one hS)).trans hceil)
  have hgamma :=
    (scaled_gamma_growth_le_linear_scale q hq η t G hη.le hηone hG).trans
      ((mul_le_mul_of_nonneg_right hDG (add_nonneg zero_le_one hS)).trans hceil)
  have hupper := (Nat.ceil_lt_add_one (mul_nonneg hD (add_nonneg zero_le_one hS))).le
  have hlocal' :
    completedZeroLocalLogBoundConstant * (1 + 644 * η * Real.log ((q : ℝ) * (|t| + 3))) ≤
      D * (1 + S) := by
    simpa only [S, mul_assoc] using hlocal
  refine ⟨hNfour, Nat.ceil_le_ceil hlocal', hmass, hgamma, ?_⟩
  nlinarith only [hupper, hL]

/-- There is an absolute positive coefficient such that every primitive near-one
zero at an admissibly small positive shift has a count cap bounded by that
coefficient times `1+η log(q(|t|+3))`, and an ordinary logarithmic-derivative signal
at order `3N` through `4N-1`. Construct the explicit ceiling cap and apply the
linear-order detector. No unproved analytic or numerical cap hypothesis remains. -/
theorem exists_ordinary_LFunction_linear_scale_detector :
    ∃ D : ℝ,
      0 < D ∧
        ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
          2 ≤ q →
            χ ≠ 1 →
            χ.IsPrimitive →
            χ⁻¹ ≠ 1 →
            ∀ {η : ℝ},
              0 < η →
                η ≤ 1 / 1288 →
                ∀ {c ρ : ℂ},
                  c.re = 1 + η →
                    c.im = ρ.im →
                    |ρ.re - 1| ≤ η →
                    χ.completedLFunction ρ = 0 →
                    χ.completedLFunction c ≠ 0 →
                    ∃ N n : ℕ,
                      4 ≤ N ∧
                        (N : ℝ) ≤ D * (1 + η * Real.log ((q : ℝ) * (|ρ.im| + 3))) ∧
                        3 * N ≤ n ∧
                        n + 1 ≤ 4 * N ∧
                        1 / (32 * (160 : ℝ) ^ N * (3 : ℝ) ^ (n + 1)) ≤
                          (η ^ (n + 1) / (n.factorial : ℝ)) *
                            ‖iteratedDeriv n (fun z : ℂ ↦ logDeriv χ.LFunction z) c‖ := by
  obtain ⟨G, hG, hdetector⟩ := exists_ordinary_LFunction_linear_order_detector_of_cap
  let D := linearOrderDetectorCapCoefficient G
  have hD : 0 < D + 1 := by
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
    have hB := mul_nonneg completedGenusMassCenterConstant_pos.le (add_nonneg hlog zero_le_one)
    have hG' := mul_nonneg hG (add_nonneg hlog (by norm_num only : (0 : ℝ) ≤ 2))
    dsimp only [D, linearOrderDetectorCapCoefficient]
    linarith only [completedZeroLocalLogBoundConstant_pos, completedGenusMassShiftConstant_pos, hB,
      hG']
  refine ⟨D + 1, hD, ?_⟩
  intro q _ χ hq hχ hp hinv η hη hηsmall c ρ hcre hcim hρre hzero hc
  let N := Nat.ceil (D * (1 + η * Real.log ((q : ℝ) * (|ρ.im| + 3))))
  obtain ⟨hN, hlocalcap, hmasscap, hgammacap, hNupper⟩ :=
    linear_order_detector_numeric_caps q hq η ρ.im G hη (hηsmall.trans (by norm_num only)) hG
  obtain ⟨n, hnlow, hnupper, hsignal⟩ :=
    hdetector hq hχ hp hinv hη hηsmall hcre hcim hρre hzero hc N hN hlocalcap hmasscap hgammacap
  exact ⟨N, n, hN, hNupper, hnlow, hnupper, hsignal⟩

/-- For a positive count cap and order at most four times it, the explicit linear
cap signal is at least `exp(-log(414720) N)`. Bound the denominator by one absolute
base to the cap power. This converts the contour constants to an exponential loss. -/
theorem linear_cap_signal_ge_exp_neg (N m : ℕ) (hN : 1 ≤ N) (hm : m ≤ 4 * N) :
    Real.exp (-(Real.log 414720 * (N : ℝ))) ≤ 1 / (32 * (160 : ℝ) ^ N * (3 : ℝ) ^ m) := by
  have h32 : (32 : ℝ) ≤ (32 : ℝ) ^ N := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num only : (1 : ℝ) ≤ 32) hN
  have h3 : (3 : ℝ) ^ m ≤ ((3 : ℝ) ^ 4) ^ N := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num only) hm
  have hdenom : 32 * (160 : ℝ) ^ N * (3 : ℝ) ^ m ≤ (414720 : ℝ) ^ N := by
    calc
      _ ≤ ((32 : ℝ) ^ N * (160 : ℝ) ^ N) * ((3 : ℝ) ^ 4) ^ N :=
        mul_le_mul (mul_le_mul_of_nonneg_right h32 (pow_nonneg (by norm_num only) N)) h3
          (pow_nonneg (by norm_num only) m)
          (mul_nonneg (pow_nonneg (by norm_num only) N) (pow_nonneg (by norm_num only) N))
      _ = _ := by
        rw [← mul_pow, ← mul_pow]; norm_num only
  have hexp : Real.exp (-(Real.log 414720 * (N : ℝ))) = 1 / (414720 : ℝ) ^ N := by
    rw [Real.exp_neg, mul_comm (Real.log 414720), Real.exp_nat_mul, Real.exp_log (by norm_num only),
      one_div]
  rw [hexp]
  exact
    one_div_le_one_div_of_le
      (mul_pos (mul_pos (by norm_num only) (pow_pos (by norm_num only) N))
        (pow_pos (by norm_num only) m))
      hdenom

/-- There are absolute positive order and signal constants such that every actual
primitive near-one zero at a sufficiently small positive shift yields a positive
normalized ordinary logarithmic-derivative iterate. The order is at most an
absolute multiple of `1+η log(q(|t|+3))`, and the signal is at least the exponential
of minus another absolute multiple of that scale. Use the explicit cap construction
and exponential denominator bound. This removes the bounded scaled-height and
product-order losses before the finite high-prime detector is constructed. -/
theorem exists_ordinary_LFunction_general_scale_exponential_detector :
    ∃ A D : ℝ,
      0 < A ∧
        0 < D ∧
        ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
          2 ≤ q →
            χ ≠ 1 →
            χ.IsPrimitive →
            χ⁻¹ ≠ 1 →
            ∀ {η : ℝ},
              0 < η →
                η ≤ 1 / 1288 →
                ∀ {c ρ : ℂ},
                  c.re = 1 + η →
                    c.im = ρ.im →
                    |ρ.re - 1| ≤ η →
                    χ.completedLFunction ρ = 0 →
                    χ.completedLFunction c ≠ 0 →
                    ∃ n : ℕ,
                      0 < n ∧
                        (n + 1 : ℝ) ≤ D * (1 + η * Real.log ((q : ℝ) * (|ρ.im| + 3))) ∧
                        Real.exp (-(A * (1 + η * Real.log ((q : ℝ) * (|ρ.im| + 3))))) ≤
                          (η ^ (n + 1) / (n.factorial : ℝ)) *
                            ‖iteratedDeriv n (fun z : ℂ ↦ logDeriv χ.LFunction z) c‖ := by
  obtain ⟨D, hD, hdetector⟩ := exists_ordinary_LFunction_linear_scale_detector
  have hlog : 0 < Real.log 414720 := Real.log_pos (by norm_num only)
  refine ⟨Real.log 414720 * D, 4 * D, mul_pos hlog hD, mul_pos (by norm_num only) hD, ?_⟩
  intro q _ χ hq hχ hp hinv η hη hηsmall c ρ hcre hcim hρre hzero hc
  obtain ⟨N, n, hN, hNupper, hnlow, hnupper, hsignal⟩ :=
    hdetector hq hχ hp hinv hη hηsmall hcre hcim hρre hzero hc
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hnreal : (n + 1 : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hnupper
  have hnpos : 0 < n :=
    (lt_of_lt_of_le (by norm_num only : 0 < 3 * 4) (Nat.mul_le_mul_left 3 hN)).trans_le hnlow
  have hscale := mul_le_mul_of_nonneg_left hNupper hlog.le
  have hexp :
    Real.exp (-(Real.log 414720 * D * (1 + η * Real.log ((q : ℝ) * (|ρ.im| + 3))))) ≤
      Real.exp (-(Real.log 414720 * (N : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith only [hscale])
  refine ⟨n, hnpos, ?_, ?_⟩
  · nlinarith only [hnreal, hNupper]
  · exact
      (hexp.trans
            (linear_cap_signal_ge_exp_neg N (n + 1) ((by decide : 1 ≤ 4).trans hN) hnupper)).trans
        hsignal

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
