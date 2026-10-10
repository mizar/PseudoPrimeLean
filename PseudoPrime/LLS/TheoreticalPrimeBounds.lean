/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaKernelMass
public import PseudoPrime.LLS.TheoreticalKernelSpecialization
public import PseudoPrime.LLS.TheoreticalKernelNumerics
public import PseudoPrime.LLS.CosetPrimeBounds
public import PseudoPrime.LLS.MellinKernelUniformComparison

/-! # The gamma-kernel reduction of the theoretical prime bound

Under GRH, the proved uniform kernel comparison and rational numerical
certificates give the Section 6.2 and 6.3 prime bounds.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Proposition 6.1 and the constructed triangular kernel
bound the least outside prime for indices at least 28, with explicit relative
error. Use the Section 6.2 endpoint estimate and the midpoint cutoff transfer.
The uniform comparison is derived from GRH, with no additional analytic premise. -/
theorem triangular_large_index_prime_bound (h : ℕ) (hh : 28 ≤ h)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (ε : ℝ) (he : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (q : ℕ) [NeZero q],
        Q ≤ q →
          ∀ H : Subgroup (ZMod q)ˣ,
            H.index = h →
              ∃ p : ℕ,
                IsLeast (primesOutside q H) p ∧
                  (p : ℝ) ≤
                    (((1 + ε) * Real.log (2 * (h : ℝ)) * ((h : ℝ) - 1) * Real.log q) /
                        (2 * (h : ℝ) * (Real.log (2 * (h : ℝ)) - 4))) ^
                      2 := by
  obtain ⟨Q, hQ⟩ := triangular_large_index_cutoff_bound MellinKernel.proposition61 h hh hg ε he
  refine ⟨Q, ?_⟩
  intro q _ hq H hH
  have hproper : H ≠ ⊤ := by
    intro htop
    have hi : h = 1 := hH.symm.trans (htop ▸ Subgroup.index_top)
    have hh1 : 1 < h := lt_of_lt_of_le (by norm_num only) hh
    exact (ne_of_gt hh1) hi
  exact exists_least_prime_outside_le_of_cutoff_bound H hproper (sq_nonneg _) (hQ q hq H hH)

/-- A relative error bounded by `min ε 1` leaves strict slack in the
coefficient `1/4+ε`. Rewrite the squared quotient into the three positive
factors of Theorem 1.3, then multiply the scalar error inequality. -/
private theorem triangular_relative_error_margin {h L R e : ℝ} (hh : 1 < h) (hL : 4 < L)
    (hR : 0 < R) (he : 0 < e) :
    (((1 + min e 1) * L * (h - 1) * R) / (2 * h * (L - 4))) ^ 2 <
      (1 / 4 + e) * (1 - 1 / h) ^ 2 * (L / (L - 4)) ^ 2 * R ^ 2 := by
  have hn : h ≠ 0 := (lt_trans (by norm_num only : (0 : ℝ) < 1) hh).ne'
  have hid : (h - 1) / h = 1 - 1 / h := by rw [sub_div, div_self hn]
  have hfac :
    (((1 + min e 1) * L * (h - 1) * R) / (2 * h * (L - 4))) ^ 2 =
      ((1 + min e 1) ^ 2 / 4) * (1 - 1 / h) ^ 2 * (L / (L - 4)) ^ 2 * R ^ 2 := by
    rw [← hid]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hd0 : 0 < min e 1 := lt_min he (by norm_num only)
  have hdsq : (min e 1) ^ 2 ≤ min e 1 := by
    have hm := mul_le_mul_of_nonneg_left (min_le_right e 1) hd0.le
    nlinarith only [hm]
  have hmargin : (1 + min e 1) ^ 2 / 4 < 1 / 4 + e := by nlinarith only [hdsq, min_le_left e 1, he]
  have hb : 0 < 1 - 1 / h := by
    rw [← hid]
    exact div_pos (sub_pos.mpr hh) (lt_trans (by norm_num only) hh)
  rw [hfac]
  exact
    mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hmargin (sq_pos_of_pos hb))
        (sq_pos_of_pos (div_pos (lt_trans (by norm_num only) hL) (sub_pos.mpr hL))))
      (sq_pos_of_pos hR)

/-- Under GRH, indices at least 28 satisfy the
strict asymptotic least-prime bound stated in Theorem 1.3. The concrete
triangular kernel supplies the cutoff estimate; choosing relative error
`min ε 1` leaves a strict margin in the coefficient `1/4+ε`. The remaining
small indices below twenty-eight are handled separately. -/
theorem triangular_large_index_asymptotic_prime_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 28 ≤ h) (ε : ℝ)
    (he : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (q : ℕ) [NeZero q],
        Q ≤ q →
          ∀ H : Subgroup (ZMod q)ˣ,
            H.index = h →
              ∃ p : ℕ,
                IsLeast (primesOutside q H) p ∧
                  (p : ℝ) <
                    (1 / 4 + ε) * (1 - 1 / (h : ℝ)) ^ 2 *
                      (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2 *
                      (Real.log q) ^ 2 := by
  obtain ⟨Q, hQ⟩ :=
    triangular_large_index_prime_bound h hh hg (min ε 1) (lt_min he (by norm_num only))
  refine ⟨max Q 2, ?_⟩
  intro q _ hq H hH
  obtain ⟨p, hp', hb⟩ := hQ q ((le_max_left Q 2).trans hq) H hH
  refine ⟨p, hp', hb.trans_lt ?_⟩
  have hhR : (28 : ℝ) ≤ h := by exact_mod_cast hh
  have hqR : (1 : ℝ) < q := by
    have hq2 : 2 ≤ q := (le_max_right Q 2).trans hq
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hq2)
  exact
    triangular_relative_error_margin (lt_of_lt_of_le (by norm_num only) hhR)
      (four_lt_log_two_mul hhR) (Real.log_pos hqR) he

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For an index greater than one and a positive parameter, a rational
coefficient certificate bounds the actual inflated gamma mass. The analytic
mass estimate and monotonicity of squares transfer the strict margin.
This supplies the mass input for arbitrary certified prime coefficients. -/
theorem gamma_mass_coefficient_of_certificate (h : ℕ) (hh : 1 < h) {l c : ℝ} (hl : 0 < l)
    (hc :
      l * (((h : ℝ) - 1) * (4710471 / 10000000)) ^ 2 < c * ((h : ℝ) - 1 - h * Real.exp (-l)) ^ 2) :
    l * (((h : ℝ) - 1) * ((1 + 1 / 10000) * gammaMellinKernel.mass)) ^ 2 <
      c * ((h : ℝ) - 1 - h * Real.exp (-l)) ^ 2 := by
  apply lt_of_le_of_lt ?_ hc
  have hhR : 0 ≤ (h : ℝ) - 1 := by
    have hr : (1 : ℝ) < h := by exact_mod_cast hh
    exact sub_nonneg.mpr hr.le
  have hm : 0 ≤ (1 + 1 / 10000 : ℝ) * gammaMellinKernel.mass :=
    mul_nonneg (by norm_num only) (MellinKernel.mass_pos gammaMellinKernel).le
  have hb : (1 + 1 / 10000 : ℝ) * gammaMellinKernel.mass ≤ 4710471 / 10000000 := by
    have ht :=
      mul_le_mul_of_nonneg_left gammaMellinKernel_mass_le
        (show (0 : ℝ) ≤ 1 + 1 / 10000 by norm_num only)
    norm_num only at ht ⊢
    exact ht
  have hs := mul_self_le_mul_self (mul_nonneg hhR hm) (mul_le_mul_of_nonneg_left hb hhR)
  simpa only [pow_two] using mul_le_mul_of_nonneg_left hs hl.le

/-- Under GRH, a positive gamma parameter with positive denominator and a
strict actual-mass coefficient margin bounds every subgroup-only interval.
Proposition 6.1 followed by the squared comparison gives a threshold uniform
over moduli and subgroups of the fixed index. -/
theorem gamma_cutoff_bound_of_coefficient
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 1 < h) {l c : ℝ}
    (hl : 0 < l) (hd : 0 < (h : ℝ) - 1 - h * Real.exp (-l))
    (hc :
      l * (((h : ℝ) - 1) * ((1 + 1 / 10000) * gammaMellinKernel.mass)) ^ 2 <
        c * ((h : ℝ) - 1 - h * Real.exp (-l)) ^ 2) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ H : Subgroup (ZMod q)ˣ,
              H.index = h →
                ∀ X : ℝ,
                  0 < X →
                    (∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) →
                    X < c * (Real.log q) ^ 2 := by
  obtain ⟨Q, hQ⟩ :=
    gamma_kernel_inequality MellinKernel.proposition61 hg h hh l hl (1 / 10000) (by norm_num only)
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  intro q _ hq H hH X hX hpr
  have hq2 : 2 ≤ q := (le_max_right Q 2).trans hq
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
  have hi := hQ q ((le_max_left Q 2).trans hq) H hH X hX hpr
  apply gamma_bound_of_coefficient hX.le hl.le hlog hd _ hc
  calc
    _ ≤ _ := hi
    _ = _ := by ring

/-- Under GRH, a positive gamma parameter and a nonnegative certified
coefficient bound the least prime outside every subgroup of the fixed index
for sufficiently large moduli. Transfer the certificate to the actual mass,
then apply the cutoff bound and Dirichlet existence with the midpoint argument.
This permits sharper coefficients without changing the paper statements. -/
theorem gamma_prime_bound_of_certificate
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 1 < h) {l c : ℝ}
    (hl : 0 < l) (hc0 : 0 ≤ c) (hd : 0 < (h : ℝ) - 1 - h * Real.exp (-l))
    (hc :
      l * (((h : ℝ) - 1) * (4710471 / 10000000)) ^ 2 < c * ((h : ℝ) - 1 - h * Real.exp (-l)) ^ 2) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ H : Subgroup (ZMod q)ˣ,
              H.index = h →
                ∃ p : ℕ, IsLeast (primesOutside q H) p ∧ (p : ℝ) ≤ c * (Real.log q) ^ 2 := by
  obtain ⟨Q, hQ2, hQ⟩ :=
    gamma_cutoff_bound_of_coefficient hg h hh hl hd
      (gamma_mass_coefficient_of_certificate h hh hl hc)
  refine ⟨Q, hQ2, ?_⟩
  intro q _ hq H hH
  have hp : H ≠ ⊤ := fun ht ↦ (ne_of_gt hh) (hH.symm.trans (ht ▸ Subgroup.index_top))
  exact
    exists_least_prime_outside_le_of_cutoff_bound H hp (mul_nonneg hc0 (sq_nonneg _))
      (fun X hX hpr ↦ (hQ q hq H hH X hX hpr).le)

/-- Under GRH, for each index at least four the least outside prime is at most
`659/1000 * (log q)^2` for all sufficiently large moduli, uniformly in the
subgroup. The parameter `73/40`, the mass estimate and the exponential
certificate give a strict coefficient margin. This strengthens the gamma
bound used when reducing moduli in the small-index problem. -/
theorem gamma_prime_bound_659 (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ)
    (hh : 4 ≤ h) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ H : Subgroup (ZMod q)ˣ,
              H.index = h →
                ∃ p : ℕ,
                  IsLeast (primesOutside q H) p ∧ (p : ℝ) ≤ (659 / 1000) * (Real.log q) ^ 2 := by
  have hhR : (4 : ℝ) ≤ h := Nat.cast_le.mpr hh
  have he := gamma_four_exp_bound
  have hd : 0 < (h : ℝ) - 1 - h * Real.exp (-(73 / 40 : ℝ)) := by
    have hp :=
      mul_nonneg (sub_nonneg.mpr hhR) (by linarith only [he] : 0 ≤ 1 - Real.exp (-(73 / 40 : ℝ)))
    nlinarith only [hp, he]
  exact
    gamma_prime_bound_of_certificate hg h (lt_of_lt_of_le (by norm_num only) hh)
      (by norm_num only : (0 : ℝ) < 73 / 40) (by norm_num only) hd
      (gamma_large_index_coefficient_659 hhR)

/-- Under GRH, each index at least four has a gamma least-prime bound valid
at every positive modulus, with one finite remainder constant. Above the
analytic threshold use coefficient `659/1000`; below it, finite existence
bounds all proper subgroups at once. This uniform maximum permits reductions
whose target modulus stays bounded while the original modulus grows. -/
theorem gamma_prime_bound_659_with_finite_remainder
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 4 ≤ h) :
    ∃ B : ℕ,
      ∀ (m : ℕ) [NeZero m],
        ∀ H : Subgroup (ZMod m)ˣ,
          H.index = h →
            ∃ r : ℕ,
              IsLeast (primesOutside m H) r ∧
                (r : ℝ) ≤ max (B : ℝ) ((659 / 1000) * (Real.log m) ^ 2) := by
  obtain ⟨Q, _, hQ⟩ := gamma_prime_bound_659 hg h hh
  obtain ⟨B, hB⟩ := exists_uniform_least_prime_bound_of_modulus_le Q
  refine ⟨B, ?_⟩
  intro m _ H hH
  by_cases hm : Q ≤ m
  · obtain ⟨r, hr, hb⟩ := hQ m hm H hH
    exact ⟨r, hr, hb.trans (le_max_right _ _)⟩
  · have hp : H ≠ ⊤ := fun ht ↦
      (ne_of_gt (lt_of_lt_of_le (by norm_num only : 1 < 4) hh))
        (hH.symm.trans (ht ▸ Subgroup.index_top))
    obtain ⟨r, hr, hb⟩ := hB m (le_of_lt (lt_of_not_ge hm)) H hp
    have hbR : (r : ℝ) ≤ B := Nat.cast_le.mpr hb
    exact ⟨r, hr, hbR.trans (le_max_left _ _)⟩

/-- GRH implies the paper's Theorem 1.2. The index-dependent gamma certificates
feed the general least-prime bound; positive asymptotic error gives the strict
paper inequality. The midpoint transfer and mass estimate are shared with
the sharper coefficient bound. -/
theorem theorem12 : lls_theorem12 := by
  intro hg h hh ε he
  obtain ⟨l, hl, hd, hc⟩ := gamma_parameters_for_index h hh
  obtain ⟨Q, hQ2, hQ⟩ :=
    gamma_prime_bound_of_certificate hg h hh hl (theoreticalCoefficient_pos h).le hd hc
  refine ⟨Q, ?_⟩
  intro q _ hq H hH
  obtain ⟨p, hp, hb⟩ := hQ q hq H hH
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hQ2.trans hq)
  refine ⟨p, hp, hb.trans_lt ?_⟩
  exact mul_lt_mul_of_pos_right (lt_add_of_pos_right _ he) (sq_pos_of_pos hlog)

/-- Under GRH, indices seven through twenty-seven
satisfy the strict asymptotic least-prime bound in Theorem 1.3. Apply the
gamma-kernel reduction of Theorem 1.2 with an error smaller than the positive
gap between its coefficient and the triangular coefficient. This connects
the certified coefficient comparison to actual least primes. -/
theorem triangular_small_index_asymptotic_prime_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 7 ≤ h) (hh' : h ≤ 27)
    (ε : ℝ) (he : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (q : ℕ) [NeZero q],
        Q ≤ q →
          ∀ H : Subgroup (ZMod q)ˣ,
            H.index = h →
              ∃ p : ℕ,
                IsLeast (primesOutside q H) p ∧
                  (p : ℝ) <
                    (1 / 4 + ε) * (1 - 1 / (h : ℝ)) ^ 2 *
                      (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2 *
                      (Real.log q) ^ 2 := by
  let A :=
    (1 / 4 : ℝ) * (1 - 1 / (h : ℝ)) ^ 2 *
      (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2
  have hA : 33 / 50 < A :=
    triangularCoefficient_gt_gamma_of_small_index (by exact_mod_cast hh) (by exact_mod_cast hh')
  have hh1 : 1 < h := lt_of_lt_of_le (by norm_num only) hh
  have hc : theoreticalCoefficient h = 33 / 50 := by
    have h2 : h ≠ 2 := by
      intro hz; rw [hz] at hh; norm_num only at hh
    have h3 : h ≠ 3 := by
      intro hz; rw [hz] at hh; norm_num only at hh
    rw [theoreticalCoefficient, ite_eq_right h2, ite_eq_right h3]
  obtain ⟨Q, hQ⟩ := theorem12 hg h hh1 ((A - 33 / 50) / 2) (by linarith only [hA])
  refine ⟨max Q 2, ?_⟩
  intro q _ hq H hH
  obtain ⟨p, hp', hb⟩ := hQ q ((le_max_left Q 2).trans hq) H hH
  rw [hc] at hb
  have hq2 : 2 ≤ q := (le_max_right Q 2).trans hq
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
  have hmid : 33 / 50 + (A - 33 / 50) / 2 < A := by linarith only [hA]
  refine ⟨p, hp', hb.trans ((mul_lt_mul_of_pos_right hmid (sq_pos_of_pos hlog)).trans_le ?_)⟩
  dsimp only [A]
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [he] : (1 / 4 : ℝ) ≤ 1 / 4 + ε) (sq_nonneg _))
        (sq_nonneg _))
      (sq_nonneg _)

/-- Under GRH, Theorem 1.3's strict asymptotic
least-prime bound holds at every index at least seven. For indices seven
through twenty-seven, use the gamma kernel and the coefficient comparison;
for larger indices, use the concrete triangular kernel. This completes the
two-range reduction while leaving indices four through six separate. -/
theorem triangular_asymptotic_prime_bound_of_index_ge_seven
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh : 7 ≤ h) (ε : ℝ)
    (he : 0 < ε) :
    ∃ Q : ℕ,
      ∀ (q : ℕ) [NeZero q],
        Q ≤ q →
          ∀ H : Subgroup (ZMod q)ˣ,
            H.index = h →
              ∃ p : ℕ,
                IsLeast (primesOutside q H) p ∧
                  (p : ℝ) <
                    (1 / 4 + ε) * (1 - 1 / (h : ℝ)) ^ 2 *
                      (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2 *
                      (Real.log q) ^ 2 := by
  by_cases hh28 : 28 ≤ h
  · exact triangular_large_index_asymptotic_prime_bound hg h hh28 ε he
  · exact
      triangular_small_index_asymptotic_prime_bound hg h hh (Nat.le_of_lt_succ (lt_of_not_ge hh28))
        ε he

end PseudoPrime.LLS.PaperStatements
