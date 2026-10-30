/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.SmallIndexConductorBounds

/-! # Uniform conductor-ratio bounds preserving index-specific kernel coefficients -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For h>1, nonnegative L,S and positive epsilon, a conductor budget
S<=r(h-1)L bounds the squared radius by (r sqrt(c)+epsilon)^2 L^2.
Cancel h-1 before squaring the nonnegative radius. Kernel-specific consumers reuse
this scalar step without weakening their certificates to a common coefficient. -/
theorem conductor_ratio_radius_le {h : ℕ} (hh : 1 < h) {c r ε L S : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L) (hS : 0 ≤ S) (hb : S ≤ r * ((h : ℝ) - 1) * L) :
    (Real.sqrt c / ((h : ℝ) - 1) * S + ε * L) ^ 2 ≤
      (r * Real.sqrt c + ε) ^ 2 * L ^ 2 := by
  have hhR : (1 : ℝ) < h := by exact_mod_cast hh
  have hf : 0 ≤ Real.sqrt c / ((h : ℝ) - 1) :=
    div_nonneg (Real.sqrt_nonneg c) (sub_nonneg.mpr hhR.le)
  have hi : Real.sqrt c / ((h : ℝ) - 1) * (r * ((h : ℝ) - 1)) = r * Real.sqrt c := by
    rw [mul_comm r ((h : ℝ) - 1), ← mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr hhR.ne')]
    exact mul_comm _ _
  have hm := mul_le_mul_of_nonneg_left hb hf
  rw [← mul_assoc, hi] at hm
  have hpos := add_nonneg (mul_nonneg hf hS) (mul_nonneg hε.le hL)
  have ht : Real.sqrt c / ((h : ℝ) - 1) * S + ε * L ≤
      (r * Real.sqrt c + ε) * L := by nlinarith only [hm]
  have hs := mul_self_le_mul_self hpos ht
  nlinarith only [hs]

/-- For c>0,r>=0 and c r^2<C, a positive ambient allowance preserves the strict
target coefficient C. Choose half the gap between r sqrt(c) and sqrt(C).
This arithmetic lemma supplies a uniform allowance independent of the modulus or subgroup. -/
theorem exists_conductor_ratio_allowance {c r C : ℝ} (hc : 0 < c) (hr : 0 ≤ r)
    (hgap : c * r ^ 2 < C) : ∃ ε : ℝ, 0 < ε ∧ (r * Real.sqrt c + ε) ^ 2 < C := by
  have hC : 0 < C := (mul_nonneg hc.le (sq_nonneg r)).trans_lt hgap
  have hs : (r * Real.sqrt c) ^ 2 < (Real.sqrt C) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hC.le]
    nlinarith only [hgap]
  have hroot : r * Real.sqrt c < Real.sqrt C :=
    (sq_lt_sq₀ (mul_nonneg hr (Real.sqrt_nonneg c)) (Real.sqrt_nonneg C)).mp hs
  refine ⟨(Real.sqrt C - r * Real.sqrt c) / 2, by linarith only [hroot], ?_⟩
  have hpos := mul_nonneg hr (Real.sqrt_nonneg c)
  have hsquare := mul_self_lt_mul_self
    (by linarith only [hpos, hroot] : 0 ≤ r * Real.sqrt c +
      (Real.sqrt C - r * Real.sqrt c) / 2)
    (by linarith only [hroot] : r * Real.sqrt c +
      (Real.sqrt C - r * Real.sqrt c) / 2 < Real.sqrt C)
  nlinarith only [hsquare, Real.sq_sqrt hC.le]

/-- Given a uniform least-prime conductor-radius bound for every positive allowance,
a fixed ratio r with c r^2<C yields a strict C log(q)^2 bound under the conductor budget.
Choose the allowance independently of q,H, then apply the scalar radius comparison.
This transport supports Gamma and the new rational-pole kernels with identical quantifiers. -/
theorem least_prime_bound_of_conductor_ratio {h : ℕ} (hh : 1 < h) {c r C : ℝ}
    (hc : 0 < c) (hr : 0 ≤ r) (hgap : c * r ^ 2 < C)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, 20000 ≤ Q ∧
      ∀ (q : ℕ) [NeZero q], Q ≤ q → ∀ H : Subgroup (ZMod q)ˣ, H.index = h →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤
          (Real.sqrt c / ((h : ℝ) - 1) * subgroupConductorLogSum H + ε * Real.log q) ^ 2) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = h →
        subgroupConductorLogSum H ≤ r * ((h : ℝ) - 1) * Real.log q →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) < C * (Real.log q) ^ 2 := by
  obtain ⟨ε, hε, hcoef⟩ := exists_conductor_ratio_allowance hc hr hgap
  obtain ⟨Q, hQ, hb⟩ := hbound ε hε
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H hi hsum
  obtain ⟨p, hp, hpb⟩ := hb q hq H hi
  have hl : 0 < Real.log q := Real.log_pos
    (by exact_mod_cast ((by norm_num only : 2 ≤ 20000).trans (hQ.trans hq)))
  exact ⟨p, hp, (hpb.trans (conductor_ratio_radius_le hh hε hl.le
    (subgroupConductorLogSum_nonneg H) hsum)).trans_lt
      (mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hl))⟩

/-- Under GRH, the index-5 Gamma certificate retains coefficient 6336 / 10000 for every
positive ambient allowance. Apply the existing numerical certificate directly, without
weakening it to the index-four coefficient. The threshold is uniform over all subgroups. -/
theorem gamma_conductor_bound_of_index_five
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 5 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤
          (Real.sqrt (6336 / 10000) / ((5 : ℝ) - 1) * subgroupConductorLogSum H +
            ε * Real.log q) ^ 2 := by
  apply gamma_prime_bound_of_conductor_certificate hg 5 (by norm_num only)
    (l := (171 / 100 : ℝ)) (c := (6336 / 10000 : ℝ))
    (by norm_num only) (by norm_num only) hε
  · have he := refined_gamma_five_exp_bound
    norm_num only
    linarith only [he]
  · have hc := refined_gamma_five_coefficient
    norm_num only at hc ⊢
    exact hc

/-- Under GRH, the index-6 Gamma certificate retains coefficient 6183 / 10000 for every
positive ambient allowance. Apply the existing numerical certificate directly, without
weakening it to the index-four coefficient. The threshold is uniform over all subgroups. -/
theorem gamma_conductor_bound_of_index_six
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 6 → ∃ p : ℕ,
        IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤
          (Real.sqrt (6183 / 10000) / ((6 : ℝ) - 1) * subgroupConductorLogSum H +
            ε * Real.log q) ^ 2 := by
  apply gamma_prime_bound_of_conductor_certificate hg 6 (by norm_num only)
    (l := (1633 / 1000 : ℝ)) (c := (6183 / 10000 : ℝ))
    (by norm_num only) (by norm_num only) hε
  · have he := refined_gamma_six_exp_bound
    norm_num only
    linarith only [he]
  · have hc := refined_gamma_six_coefficient
    norm_num only at hc ⊢
    exact hc

/-- For L between l>0 and four, a rational lower endpoint certifies a squared
log-ratio coefficient. Bound L^2 below and (L-4)^2 above before clearing the positive
denominator. This small scalar lemma avoids new logarithm tables. -/
theorem coefficient_lt_of_log_lower {a c l L : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hl : 0 < l) (hlo : l ≤ L) (hhi : L < 4)
    (hcert : c * (l - 4) ^ 2 < a * l ^ 2) : c < a * (L / (L - 4)) ^ 2 := by
  have hd : (L - 4) ≠ 0 := sub_ne_zero.mpr (ne_of_lt hhi)
  have hs : (L - 4) ^ 2 ≤ (l - 4) ^ 2 := by
    nlinarith only [hlo, hhi, mul_nonneg (sub_nonneg.mpr hlo)
      (by linarith only [hlo, hhi] : 0 ≤ 8 - l - L)]
  have hnum := mul_le_mul_of_nonneg_left (mul_self_le_mul_self hl.le hlo) ha
  have hden := mul_le_mul_of_nonneg_left hs hc
  rw [div_pow, ← mul_div_assoc, lt_div_iff₀ (sq_pos_of_ne_zero hd)]
  nlinarith only [hnum, hden, hcert]

/-- For index 5, the retained Gamma coefficient and conductor ratio 2 / 3 leave a
strict margin below the original Theorem 1.3 coefficient. Certified logarithms and
one rational comparison establish the margin without decimal assumptions. -/
theorem gamma_index_five_ratio_gap :
    (6336 / 10000 : ℝ) * (2 / 3) ^ 2 < (1 / 4) * (1 - 1 / (5 : ℝ)) ^ 2 *
      (Real.log (2 * (5 : ℝ)) / (Real.log (2 * (5 : ℝ)) - 4)) ^ 2 := by
  have hid : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    have hi := Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0)
      (by norm_num only : (5 : ℝ) ≠ 0)
    norm_num only at hi
    exact hi
  norm_num only
  apply coefficient_lt_of_log_lower (l := (23 / 10 : ℝ))
    (by norm_num only) (by norm_num only) (by norm_num only)
  · rw [hid]
    linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · rw [hid]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  · norm_num only

/-- Under GRH, the index-5 conductor condition S_H<=(2 / 3)(h-1)log q yields the
original strict leading coefficient of Theorem 1.3 uniformly for sufficiently large q.
Retain the index-specific certificate and consume its certified ratio gap. This is a
conditional arithmetic branch, not the unrestricted index-5 theorem. -/
theorem theorem13_index_five_conductor_ratio
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 5 →
        subgroupConductorLogSum H ≤ (2 / 3 : ℝ) * ((5 : ℝ) - 1) * Real.log q →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) <
          (1 / 4) * (1 - 1 / (5 : ℝ)) ^ 2 *
            (Real.log (2 * (5 : ℝ)) / (Real.log (2 * (5 : ℝ)) - 4)) ^ 2 *
              (Real.log q) ^ 2 := by
  exact least_prime_bound_of_conductor_ratio (by norm_num only : 1 < 5)
    (by norm_num only : (0 : ℝ) < 6336 / 10000) (by norm_num only : (0 : ℝ) ≤ 2 / 3)
    gamma_index_five_ratio_gap (fun _ hε ↦ gamma_conductor_bound_of_index_five hg hε)

/-- For index 6, the retained Gamma coefficient and conductor ratio 6 / 7 leave a
strict margin below the original Theorem 1.3 coefficient. Certified logarithms and
one rational comparison establish the margin without decimal assumptions. -/
theorem gamma_index_six_ratio_gap :
    (6183 / 10000 : ℝ) * (6 / 7) ^ 2 < (1 / 4) * (1 - 1 / (6 : ℝ)) ^ 2 *
      (Real.log (2 * (6 : ℝ)) / (Real.log (2 * (6 : ℝ)) - 4)) ^ 2 := by
  have hid : Real.log (12 : ℝ) = 2 * Real.log 2 + Real.log 3 := by
    have hi := Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0)
      (by norm_num only : (3 : ℝ) ≠ 0)
    have hi4 := Real.log_pow (2 : ℝ) 2
    norm_num only at hi hi4
    rw [hi, hi4]
  norm_num only
  apply coefficient_lt_of_log_lower (l := (62 / 25 : ℝ))
    (by norm_num only) (by norm_num only) (by norm_num only)
  · rw [hid]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  · rw [hid]
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  · norm_num only

/-- Under GRH, the index-6 conductor condition S_H<=(6 / 7)(h-1)log q yields the
original strict leading coefficient of Theorem 1.3 uniformly for sufficiently large q.
Retain the index-specific certificate and consume its certified ratio gap. This is a
conditional arithmetic branch, not the unrestricted index-6 theorem. -/
theorem theorem13_index_six_conductor_ratio
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 6 →
        subgroupConductorLogSum H ≤ (6 / 7 : ℝ) * ((6 : ℝ) - 1) * Real.log q →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) <
          (1 / 4) * (1 - 1 / (6 : ℝ)) ^ 2 *
            (Real.log (2 * (6 : ℝ)) / (Real.log (2 * (6 : ℝ)) - 4)) ^ 2 *
              (Real.log q) ^ 2 := by
  exact least_prime_bound_of_conductor_ratio (by norm_num only : 1 < 6)
    (by norm_num only : (0 : ℝ) < 6183 / 10000) (by norm_num only : (0 : ℝ) ≤ 6 / 7)
    gamma_index_six_ratio_gap (fun _ hε ↦ gamma_conductor_bound_of_index_six hg hε)

end PseudoPrime.LLS.PaperStatements
