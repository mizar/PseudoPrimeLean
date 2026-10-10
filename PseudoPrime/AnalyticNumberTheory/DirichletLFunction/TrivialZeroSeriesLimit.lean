/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TrivialZeroMultiplicity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HeightRectangle

/-!
# Finite trivial-zero supports in the common Dirichlet rectangles

Left edges at `-2m-1/2` include exactly the first `m` nonzero trivial zeros of
either parity. The exact support connects multiplicity-one residues to series.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- A real point belongs to the generic rectangle precisely when its real
coordinate lies between the left edge and two. The positive height contains
the real axis; the orientation excludes the reversed closed intervals. -/
theorem real_mem_primitiveHeightRectangle_iff {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A k : ℕ) (hA : 2 ≤ A) (r : ℝ) :
    (r : ℂ) ∈
        Rectangle.rectangleClosedBox (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv A k)
          (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv k) ↔
      -(A : ℝ) - 1 / 2 ≤ r ∧ r ≤ 2 := by
  obtain ⟨hreL, himL, hreU, himU, _, _⟩ :=
    primitiveHeightSeqRectangleFacts hN2 hGRH hp hne hinv A k hA
  have ht : 0 < primitiveHorizontalHeightSeq hN2 hGRH hp hne hinv k := by
    have h := primitiveHorizontalHeightSeq_ge hN2 hGRH hp hne hinv k
    linarith only [h, Nat.cast_nonneg (α := ℝ) k]
  simp only [Rectangle.rectangleClosedBox, Complex.mem_reProdIm, Set.mem_uIcc, Complex.ofReal_re,
    Complex.ofReal_im, hreL, himL, hreU, himU, primitiveReciprocalLeftRe]
  constructor
  · intro h
    rcases h.1 with h | h
    · exact h
    · have ha : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
      exact False.elim (by linarith only [h.1, h.2, ha])
  · intro h
    exact ⟨Or.inl h, Or.inl ⟨neg_nonpos.mpr ht.le, ht.le⟩⟩

/-- Under GRH for a primitive nonprincipal character and its nonprincipal inverse, with
m >= 1 and parity parameter a <= 1, the location -2(j+1)+a is in the selected rectangle
with left edge -2m-1/2 exactly when j < m. Positive height reduces membership to the
real coordinate inequalities. This gives a common cutoff for both parity series. -/
theorem trivialLocation_mem_primitiveHeightRectangle_iff {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (m k j a : ℕ) (hm : 1 ≤ m) (ha : a ≤ 1) :
    (-2 * ((j : ℂ) + 1) + (a : ℂ)) ∈
        Rectangle.rectangleClosedBox (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) k)
          (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv k) ↔
      j < m := by
  have hA : 2 ≤ 2 * m := Nat.mul_le_mul_left 2 hm
  have hc : (-2 * ((j : ℂ) + 1) + (a : ℂ)) = ((-2 * ((j : ℝ) + 1) + (a : ℝ) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one]
  rw [hc, real_mem_primitiveHeightRectangle_iff hN2 hGRH hp hne hinv (2 * m) k hA]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have han : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have ha1 : (a : ℝ) ≤ 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_le.mpr ha : (a : ℝ) ≤ (1 : ℕ))
  have hjn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor
  · intro h
    have hjm : (j : ℝ) < m := by linarith only [h.1, ha1]
    exact Nat.cast_lt.mp hjm
  · intro h
    have hjm : (j : ℝ) + 1 ≤ m := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_le.mpr (Nat.succ_le_of_lt h) : ((j + 1 : ℕ) : ℝ) ≤ m)
    exact ⟨by linarith only [hjm, han], by linarith only [hjn, ha1]⟩

/-- For an even character, every nonzero gamma-forced point is a negative even
integer indexed from one. This classification fixes the logarithmic and
reciprocal correction-series indices without assumptions on the character level. -/
theorem exists_nat_trivial_location_of_even {N : ℕ} {χ : DirichletCharacter ℂ N} (he : χ.Even)
    {ρ : ℂ} (hΓ : DirichletCharacter.gammaFactor χ ρ = 0) (hρ : ρ ≠ 0) :
    ∃ j : ℕ, ρ = -2 * ((j : ℂ) + 1) := by
  rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
  obtain ⟨n, hn⟩ := hΓ
  cases n with
  | zero => exact False.elim (hρ (by simpa only [Nat.cast_zero, mul_zero, neg_zero] using hn))
  | succ j => exact ⟨j, by simpa only [Nat.cast_succ, neg_mul] using hn⟩

/-- For an odd character, gamma-forced points are negative odd integers indexed
from zero. The translation in `Gammaℝ(s+1)` determines the index convention
used in both odd correction series. -/
theorem exists_nat_trivial_location_of_odd {N : ℕ} {χ : DirichletCharacter ℂ N} (ho : χ.Odd) {ρ : ℂ}
    (hΓ : DirichletCharacter.gammaFactor χ ρ = 0) : ∃ j : ℕ, ρ = -2 * ((j : ℂ) + 1) + 1 := by
  rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
  obtain ⟨n, hn⟩ := hΓ
  refine ⟨n, ?_⟩
  calc
    ρ = -(2 * (n : ℂ)) - 1 := eq_sub_of_add_eq hn
    _ = -2 * ((n : ℂ) + 1) + 1 := by ring

/-- The nonzero gamma-forced zero ledger for an even character is exactly the
image of `range m` at the negative even locations. Rectangle membership and
the totalized completed-to-ordinary identity prove both inclusions. -/
theorem even_trivialZeros_primitiveRectangle_eq_image {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even) (m k : ℕ) (hm : 1 ≤ m) :
    (dirichletLFunctionZerosInRectangle χ hne
            (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) k)
            (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv k)).filter
        (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0) =
      (Finset.range m).image (fun j : ℕ => -2 * ((j : ℂ) + 1)) := by
  classical
  ext ρ
  constructor
  · intro h
    obtain ⟨hZ, hΓ, hρ⟩ := Finset.mem_filter.mp h
    obtain ⟨j, hj⟩ := exists_nat_trivial_location_of_even he hΓ hρ
    have hb := (mem_dirichletLFunctionZerosInRectangle_iff.mp hZ).1
    have hmem :=
      (trivialLocation_mem_primitiveHeightRectangle_iff hN2 hGRH hp hne hinv m k j 0 hm
            (Nat.zero_le 1)).mp
        (by
          simpa only [dirichletCompletedLFunctionRectangleBox, Nat.cast_zero, add_zero, ← hj] using
            hb)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hmem, hj.symm⟩
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    have hΓ : DirichletCharacter.gammaFactor χ (-2 * ((j : ℂ) + 1)) = 0 := by
      rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
      exact ⟨j + 1, by rw [Nat.cast_add, Nat.cast_one, neg_mul]⟩
    have hz : -2 * ((j : ℂ) + 1) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero j)
    refine Finset.mem_filter.mpr ⟨mem_dirichletLFunctionZerosInRectangle_iff.mpr ⟨?_, ?_⟩, hΓ, hz⟩
    · simpa only [dirichletCompletedLFunctionRectangleBox, Nat.cast_zero, add_zero] using
        (trivialLocation_mem_primitiveHeightRectangle_iff hN2 hGRH hp hne hinv m k j 0 hm
              (Nat.zero_le 1)).mpr
          (Finset.mem_range.mp hj)
    · rw [dirichletLFunction_eq_completed_div_gammaFactor χ _
          (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne)),
        hΓ, div_zero]

/-- The gamma-forced zero ledger for an odd character is exactly the image of
`range m` at the negative odd locations. It contains no zero at the origin,
so this is the complete trivial-zero contribution to either Mellin kernel. -/
theorem odd_trivialZeros_primitiveRectangle_eq_image {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ho : χ.Odd) (m k : ℕ) (hm : 1 ≤ m) :
    (dirichletLFunctionZerosInRectangle χ hne
            (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) k)
            (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv k)).filter
        (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0) =
      (Finset.range m).image (fun j : ℕ => -2 * ((j : ℂ) + 1) + 1) := by
  classical
  ext ρ
  constructor
  · intro h
    obtain ⟨hZ, hΓ, _⟩ := Finset.mem_filter.mp h
    obtain ⟨j, hj⟩ := exists_nat_trivial_location_of_odd ho hΓ
    have hb := (mem_dirichletLFunctionZerosInRectangle_iff.mp hZ).1
    have hmem :=
      (trivialLocation_mem_primitiveHeightRectangle_iff hN2 hGRH hp hne hinv m k j 1 hm
            (Nat.le_refl 1)).mp
        (by simpa only [dirichletCompletedLFunctionRectangleBox, Nat.cast_one, ← hj] using hb)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hmem, hj.symm⟩
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    have hΓ : DirichletCharacter.gammaFactor χ (-2 * ((j : ℂ) + 1) + 1) = 0 := by
      rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
      exact ⟨j, by ring⟩
    have hz : -2 * ((j : ℂ) + 1) + 1 ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat,
        Complex.natCast_re, Complex.one_re, Complex.zero_re, Complex.neg_im] at hre
      linarith only [hre, Nat.cast_nonneg (α := ℝ) j]
    refine Finset.mem_filter.mpr ⟨mem_dirichletLFunctionZerosInRectangle_iff.mpr ⟨?_, ?_⟩, hΓ, hz⟩
    · simpa only [dirichletCompletedLFunctionRectangleBox, Nat.cast_one] using
        (trivialLocation_mem_primitiveHeightRectangle_iff hN2 hGRH hp hne hinv m k j 1 hm
              (Nat.le_refl 1)).mpr
          (Finset.mem_range.mp hj)
    · rw [dirichletLFunction_eq_completed_div_gammaFactor χ _
          (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne)),
        hΓ, div_zero]

/-- At a negative integer, the logarithmic kernel equals the real inverse-power
summand for every real `x`, using totalized division and integer complex powers.
This common identity serves both parity conventions. -/
theorem log_kernel_neg_nat (x : ℝ) (n : ℕ) :
    -(x : ℂ) ^ (-(n : ℂ)) / (-(n : ℂ)) ^ 2 = -((x⁻¹ ^ n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [Complex.cpow_neg, Complex.cpow_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_inv, inv_pow]
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, neg_sq, neg_div]

/-- The reciprocal kernel at a negative integer is the real inverse-power
summand with exponent `n+1` and denominator `n*(n+1)`. This is the exact
summand needed for the reciprocal trivial-zero correction series. -/
theorem reciprocal_kernel_neg_nat (x : ℝ) (n : ℕ) :
    -(x : ℂ) ^ (-(n : ℂ) - 1) / ((-(n : ℂ)) * (-(n : ℂ) - 1)) =
      -((x⁻¹ ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  have he : -(n : ℂ) - 1 = -((n + 1 : ℕ) : ℂ) := by
    rw [Nat.cast_add, Nat.cast_one, neg_add]
    rfl
  rw [he, Complex.cpow_neg, Complex.cpow_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    inv_pow]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one, neg_mul_neg, neg_div]

/-- For a primitive nonprincipal character at a gamma-forced negative integer,
the logarithmic contribution is the real inverse-power term with coefficient
one. This connects the multiplicity theorem to the correction-series summand. -/
theorem log_trivialZeroContribution_neg_nat {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (x : ℝ) (n : ℕ)
    (hΓ : DirichletCharacter.gammaFactor χ (-(n : ℂ)) = 0) :
    dirichletLFunctionLogZeroContribution x χ (-(n : ℂ)) = -((x⁻¹ ^ n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hre : (-(n : ℂ)).re ≤ 0 := by
    simpa only [Complex.neg_re, Complex.natCast_re] using
      neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) n)
  rw [dirichletLFunctionLogZeroContribution_of_gamma_zero hp hne hre hΓ]
  exact log_kernel_neg_nat x n

/-- At a gamma-forced negative integer, the reciprocal contribution has its
exact natural inverse-power form. The result includes the coefficient-one
multiplicity and serves the finite reciprocal correction sums. -/
theorem reciprocal_trivialZeroContribution_neg_nat {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (x : ℝ) (n : ℕ)
    (hΓ : DirichletCharacter.gammaFactor χ (-(n : ℂ)) = 0) :
    dirichletLFunctionReciprocalZeroContribution x χ (-(n : ℂ)) =
      -((x⁻¹ ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  have hre : (-(n : ℂ)).re ≤ 0 := by
    simpa only [Complex.neg_re, Complex.natCast_re] using
      neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) n)
  rw [dirichletLFunctionReciprocalZeroContribution_of_gamma_zero hp hne hre hΓ]
  exact reciprocal_kernel_neg_nat x n

/-- Summing gamma-forced logarithmic residues over negative natural locations
gives exactly the negative real partial series. Injectivity removes duplicate
locations, and the multiplicity-one formula fixes every coefficient. -/
theorem sum_log_trivialZeroContributions_neg_nat {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (x : ℝ) (S : Finset ℕ)
    (hΓ : ∀ n ∈ S, DirichletCharacter.gammaFactor χ (-(n : ℂ)) = 0) :
    (∑ ρ ∈ S.image (fun n : ℕ => -(n : ℂ)), dirichletLFunctionLogZeroContribution x χ ρ) =
      -((∑ n ∈ S, x⁻¹ ^ n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [Finset.sum_image (fun a _ b _ h => Nat.cast_injective (R := ℂ) (neg_injective h)),
    Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun n hn => log_trivialZeroContribution_neg_nat hp hne x n (hΓ n hn))

/-- The reciprocal residue sum at negative natural locations is exactly its
negative real partial series. This finite identity preserves the full
correction before taking any height or left-edge limit. -/
theorem sum_reciprocal_trivialZeroContributions_neg_nat {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (x : ℝ) (S : Finset ℕ)
    (hΓ : ∀ n ∈ S, DirichletCharacter.gammaFactor χ (-(n : ℂ)) = 0) :
    (∑ ρ ∈ S.image (fun n : ℕ => -(n : ℂ)), dirichletLFunctionReciprocalZeroContribution x χ ρ) =
      -((∑ n ∈ S, x⁻¹ ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  classical
  rw [Finset.sum_image (fun a _ b _ h => Nat.cast_injective (R := ℂ) (neg_injective h)),
    Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  exact
    Finset.sum_congr rfl
      (fun n hn => reciprocal_trivialZeroContribution_neg_nat hp hne x n (hΓ n hn))

/-- The logarithmic inverse-power terms over all natural exponents are summable
for `x > 1`. Their nonnegative denominator-weighted terms are bounded by the
geometric series, allowing either parity subsequence to converge. -/
theorem summable_log_inversePower_nat {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => x⁻¹ ^ n / (n : ℝ) ^ 2) := by
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr ((zero_lt_one.trans hx).le)
  have hg := summable_geometric_of_lt_one hi (inv_lt_one_of_one_lt₀ hx)
  refine hg.of_nonneg_of_le (fun n => div_nonneg (pow_nonneg hi n) (sq_nonneg (n : ℝ))) ?_
  intro n
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_pow (of_decide_eq_true rfl : (2 : ℕ) ≠ 0), div_zero, pow_zero,
      zero_le_one]
  | succ n =>
    have hn : 1 ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hd : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith only [hn]
    simp only [Nat.cast_succ]
    exact div_le_self (pow_nonneg hi _) hd

/-- The reciprocal inverse-power terms over all natural exponents are summable
for `x > 1`. The zero-denominator term at zero is totalized to zero; every
remaining denominator is at least one and permits geometric domination. -/
theorem summable_reciprocal_inversePower_nat {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => x⁻¹ ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1))) := by
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr ((zero_lt_one.trans hx).le)
  have hg : Summable (fun n : ℕ => x⁻¹ ^ (n + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one hi (inv_lt_one_of_one_lt₀ hx)).mul_right x⁻¹
  refine
    hg.of_nonneg_of_le
      (fun n =>
        div_nonneg (pow_nonneg hi _)
          (mul_nonneg (Nat.cast_nonneg n) (add_nonneg (Nat.cast_nonneg n) zero_le_one)))
      ?_
  intro n
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, div_zero]; exact pow_nonneg hi _
  | succ n =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd : 1 ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) + 1) := by nlinarith only [hn]
    simp only [Nat.cast_succ]
    exact div_le_self (pow_nonneg hi _) hd

/-- Removing the two Mellin points from the singularity ledger leaves exactly
the nonzero ordinary gamma-forced zeros in its trivial part. Gamma zeros
have nonpositive real part, so one cannot contribute to this filter. -/
theorem erased_gammaZeros_eq_trivialZeroFilter {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (z w : ℂ) :
    (((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0).filter
        (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0) =
      (dirichletLFunctionZerosInRectangle χ hne z w).filter
        (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0) := by
  classical
  ext ρ
  constructor
  · intro h
    obtain ⟨hmem, hΓ⟩ := Finset.mem_filter.mp h
    obtain ⟨hρ0, hmem⟩ := Finset.mem_erase.mp hmem
    obtain ⟨hρ1, hmem⟩ := Finset.mem_erase.mp hmem
    obtain ⟨hb, hzero | hone | hL⟩ := mem_dirichletLFunctionSingularitiesInRectangle_iff.mp hmem
    · exact False.elim (hρ0 hzero)
    · exact False.elim (hρ1 hone)
    · exact Finset.mem_filter.mpr ⟨mem_dirichletLFunctionZerosInRectangle_iff.mpr ⟨hb, hL⟩, hΓ, hρ0⟩
  · intro h
    obtain ⟨hZ, hΓ, hρ0⟩ := Finset.mem_filter.mp h
    obtain ⟨hb, hL⟩ := mem_dirichletLFunctionZerosInRectangle_iff.mp hZ
    have hρ1 : ρ ≠ 1 := by
      intro h1
      have hre := gammaFactor_zero_re_nonpos hΓ
      rw [h1, Complex.one_re] at hre
      exact (not_le_of_gt zero_lt_one) hre
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr
            ⟨hρ0,
              Finset.mem_erase.mpr
                ⟨hρ1,
                  mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr ⟨hb, Or.inr (Or.inr hL)⟩⟩⟩,
          hΓ⟩

/-- The even logarithmic trivial-zero sum in the common rectangle is exactly
the negative complex cast of the first `m` even inverse-power terms. The
support theorem and multiplicity-one summands keep the full correction. -/
theorem sum_even_log_trivialZeros_primitiveRectangle_eq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even) (x : ℝ) (m k : ℕ) (hm : 1 ≤ m) :
    (∑
        ρ ∈
          (dirichletLFunctionZerosInRectangle χ hne
                (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) k)
                (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv k)).filter
            (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
        dirichletLFunctionLogZeroContribution x χ ρ) =
      -((∑ j ∈ Finset.range m, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [even_trivialZeros_primitiveRectangle_eq_image hN2 hGRH hp hne hinv he m k hm,
    Finset.sum_image
      (fun a _ b _ h =>
        Nat.cast_injective (R := ℂ)
          (add_right_cancel (mul_left_cancel₀ (neg_ne_zero.mpr two_ne_zero) h))),
    Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hloc : -2 * ((j : ℂ) + 1) = -((2 * (j + 1) : ℕ) : ℂ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, neg_mul]
  have hΓ : DirichletCharacter.gammaFactor χ (-((2 * (j + 1) : ℕ) : ℂ)) = 0 := by
    rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
    exact ⟨j + 1, by rw [Nat.cast_mul, Nat.cast_ofNat]⟩
  rw [hloc]
  exact log_trivialZeroContribution_neg_nat hp hne x (2 * (j + 1)) hΓ

/-- The odd logarithmic trivial-zero sum is the negative complex cast of the
first `m` odd inverse-power terms. The exact support and simple-zero theorem
determine every term, independently of the height index. -/
theorem sum_odd_log_trivialZeros_primitiveRectangle_eq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ho : χ.Odd) (x : ℝ) (m k : ℕ) (hm : 1 ≤ m) :
    (∑
        ρ ∈
          (dirichletLFunctionZerosInRectangle χ hne
                (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) k)
                (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv k)).filter
            (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
        dirichletLFunctionLogZeroContribution x χ ρ) =
      -((∑ j ∈ Finset.range m, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [odd_trivialZeros_primitiveRectangle_eq_image hN2 hGRH hp hne hinv ho m k hm,
    Finset.sum_image
      (fun a _ b _ h =>
        Nat.cast_injective (R := ℂ)
          (add_right_cancel (mul_left_cancel₀ (neg_ne_zero.mpr two_ne_zero) (add_right_cancel h)))),
    Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hloc : -2 * ((j : ℂ) + 1) + 1 = -((2 * j + 1 : ℕ) : ℂ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  have hΓ : DirichletCharacter.gammaFactor χ (-((2 * j + 1 : ℕ) : ℂ)) = 0 := by
    rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
    exact
      ⟨j, by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]; ring⟩
  rw [hloc]
  exact log_trivialZeroContribution_neg_nat hp hne x (2 * j + 1) hΓ

/-- As the left edge expands, the even logarithmic trivial-zero ledger
converges to its full correction series for `x > 1`, along any height-index
selection. The exact finite support and summable even subsequence give the limit. -/
theorem tendsto_sum_even_log_trivialZeros_primitiveRectangle {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even) {x : ℝ} (hx : 1 < x) (g : ℕ → ℕ) :
    Filter.Tendsto
      (fun m =>
        ∑
          ρ ∈
            (dirichletLFunctionZerosInRectangle χ hne
                  (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) (g m))
                  (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv (g m))).filter
              (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
          dirichletLFunctionLogZeroContribution x χ ρ)
      Filter.atTop
      (nhds (-((∑' j : ℕ, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))) := by
  have hi : Function.Injective (fun j : ℕ => 2 * (j + 1)) := by
    intro a b h
    exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left (of_decide_eq_true rfl : 0 < 2) h)
  have hs := (summable_log_inversePower_nat hx).comp_injective hi
  have ht :
    Filter.Tendsto
      (fun m =>
        -((∑ j ∈ Finset.range m, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))
      Filter.atTop
      (nhds (-((∑' j : ℕ, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))) := by
    simpa only [Complex.ofReal_neg, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto _).comp hs.hasSum.tendsto_sum_nat.neg
  exact
    ht.congr'
      (by
        filter_upwards [Filter.eventually_ge_atTop 1] with m hm
        exact
          (sum_even_log_trivialZeros_primitiveRectangle_eq hN2 hGRH hp hne hinv he x m (g m)
              hm).symm)

/-- Under GRH for a primitive nonprincipal odd character and its nonprincipal inverse,
and for x > 1, the odd logarithmic trivial-zero ledger converges to the complete odd
correction series along any height-index selection. Geometric domination proves summability;
the finite support theorem identifies the partial sums independently of height. -/
theorem tendsto_sum_odd_log_trivialZeros_primitiveRectangle {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ho : χ.Odd) {x : ℝ} (hx : 1 < x) (g : ℕ → ℕ) :
    Filter.Tendsto
      (fun m =>
        ∑
          ρ ∈
            (dirichletLFunctionZerosInRectangle χ hne
                  (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) (g m))
                  (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv (g m))).filter
              (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
          dirichletLFunctionLogZeroContribution x χ ρ)
      Filter.atTop
      (nhds (-((∑' j : ℕ, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))) := by
  have hi : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (of_decide_eq_true rfl : 0 < 2) (Nat.add_right_cancel h)
  have hs := (summable_log_inversePower_nat hx).comp_injective hi
  have ht :
    Filter.Tendsto
      (fun m => -((∑ j ∈ Finset.range m, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))
      Filter.atTop
      (nhds (-((∑' j : ℕ, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))) := by
    simpa only [Complex.ofReal_neg, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto _).comp hs.hasSum.tendsto_sum_nat.neg
  exact
    ht.congr'
      (by
        filter_upwards [Filter.eventually_ge_atTop 1] with m hm
        exact
          (sum_odd_log_trivialZeros_primitiveRectangle_eq hN2 hGRH hp hne hinv ho x m (g m)
              hm).symm)

/-- The even reciprocal trivial-zero sum in the common rectangle is exactly
the negative complex cast of the first `m` even inverse-power terms. The
support theorem and multiplicity-one summands keep the full correction. -/
theorem sum_even_reciprocal_trivialZeros_primitiveRectangle_eq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even) (x : ℝ) (m k : ℕ) (hm : 1 ≤ m) :
    (∑
        ρ ∈
          (dirichletLFunctionZerosInRectangle χ hne
                (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) k)
                (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv k)).filter
            (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
        dirichletLFunctionReciprocalZeroContribution x χ ρ) =
      -((∑ j ∈ Finset.range m,
              x⁻¹ ^ (2 * (j + 1) + 1) / (((2 * (j + 1) : ℕ) : ℝ) * (((2 * (j + 1) : ℕ) : ℝ) + 1)) :
            ℝ) :
          ℂ) := by
  classical
  rw [even_trivialZeros_primitiveRectangle_eq_image hN2 hGRH hp hne hinv he m k hm,
    Finset.sum_image
      (fun a _ b _ h =>
        Nat.cast_injective (R := ℂ)
          (add_right_cancel (mul_left_cancel₀ (neg_ne_zero.mpr two_ne_zero) h))),
    Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hloc : -2 * ((j : ℂ) + 1) = -((2 * (j + 1) : ℕ) : ℂ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, neg_mul]
  have hΓ : DirichletCharacter.gammaFactor χ (-((2 * (j + 1) : ℕ) : ℂ)) = 0 := by
    rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
    exact ⟨j + 1, by rw [Nat.cast_mul, Nat.cast_ofNat]⟩
  rw [hloc]
  exact reciprocal_trivialZeroContribution_neg_nat hp hne x (2 * (j + 1)) hΓ

/-- The odd reciprocal trivial-zero sum is the negative complex cast of the
first `m` odd inverse-power terms. The exact support and simple-zero theorem
determine every term, independently of the height index. -/
theorem sum_odd_reciprocal_trivialZeros_primitiveRectangle_eq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ho : χ.Odd) (x : ℝ) (m k : ℕ) (hm : 1 ≤ m) :
    (∑
        ρ ∈
          (dirichletLFunctionZerosInRectangle χ hne
                (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) k)
                (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv k)).filter
            (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
        dirichletLFunctionReciprocalZeroContribution x χ ρ) =
      -((∑ j ∈ Finset.range m,
              x⁻¹ ^ (2 * j + 1 + 1) / (((2 * j + 1 : ℕ) : ℝ) * (((2 * j + 1 : ℕ) : ℝ) + 1)) :
            ℝ) :
          ℂ) := by
  classical
  rw [odd_trivialZeros_primitiveRectangle_eq_image hN2 hGRH hp hne hinv ho m k hm,
    Finset.sum_image
      (fun a _ b _ h =>
        Nat.cast_injective (R := ℂ)
          (add_right_cancel (mul_left_cancel₀ (neg_ne_zero.mpr two_ne_zero) (add_right_cancel h)))),
    Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hloc : -2 * ((j : ℂ) + 1) + 1 = -((2 * j + 1 : ℕ) : ℂ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  have hΓ : DirichletCharacter.gammaFactor χ (-((2 * j + 1 : ℕ) : ℂ)) = 0 := by
    rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
    exact
      ⟨j, by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]; ring⟩
  rw [hloc]
  exact reciprocal_trivialZeroContribution_neg_nat hp hne x (2 * j + 1) hΓ

/-- As the left edge expands, the even reciprocal trivial-zero ledger
converges to its full correction series for `x > 1`, along any height-index
selection. The exact finite support and summable even subsequence give the limit. -/
theorem tendsto_sum_even_reciprocal_trivialZeros_primitiveRectangle {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even) {x : ℝ} (hx : 1 < x) (g : ℕ → ℕ) :
    Filter.Tendsto
      (fun m =>
        ∑
          ρ ∈
            (dirichletLFunctionZerosInRectangle χ hne
                  (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) (g m))
                  (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv (g m))).filter
              (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
          dirichletLFunctionReciprocalZeroContribution x χ ρ)
      Filter.atTop
      (nhds
        (-((∑' j : ℕ,
                x⁻¹ ^ (2 * (j + 1) + 1) /
                  (((2 * (j + 1) : ℕ) : ℝ) * (((2 * (j + 1) : ℕ) : ℝ) + 1)) :
              ℝ) :
            ℂ))) := by
  have hi : Function.Injective (fun j : ℕ => 2 * (j + 1)) := by
    intro a b h
    exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left (of_decide_eq_true rfl : 0 < 2) h)
  have hs := (summable_reciprocal_inversePower_nat hx).comp_injective hi
  have ht :
    Filter.Tendsto
      (fun m =>
        -((∑ j ∈ Finset.range m,
                x⁻¹ ^ (2 * (j + 1) + 1) /
                  (((2 * (j + 1) : ℕ) : ℝ) * (((2 * (j + 1) : ℕ) : ℝ) + 1)) :
              ℝ) :
            ℂ))
      Filter.atTop
      (nhds
        (-((∑' j : ℕ,
                x⁻¹ ^ (2 * (j + 1) + 1) /
                  (((2 * (j + 1) : ℕ) : ℝ) * (((2 * (j + 1) : ℕ) : ℝ) + 1)) :
              ℝ) :
            ℂ))) := by
    simpa only [Complex.ofReal_neg, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto _).comp hs.hasSum.tendsto_sum_nat.neg
  exact
    ht.congr'
      (by
        filter_upwards [Filter.eventually_ge_atTop 1] with m hm
        exact
          (sum_even_reciprocal_trivialZeros_primitiveRectangle_eq hN2 hGRH hp hne hinv he x m (g m)
              hm).symm)

/-- Under GRH for a primitive nonprincipal odd character and its nonprincipal inverse,
and for x > 1, the odd reciprocal trivial-zero ledger converges to the complete odd
correction series along any height-index selection. Geometric domination proves summability;
the finite support theorem identifies the partial sums independently of height. -/
theorem tendsto_sum_odd_reciprocal_trivialZeros_primitiveRectangle {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ho : χ.Odd) {x : ℝ} (hx : 1 < x) (g : ℕ → ℕ) :
    Filter.Tendsto
      (fun m =>
        ∑
          ρ ∈
            (dirichletLFunctionZerosInRectangle χ hne
                  (primitiveHeightSeqLowerCorner hN2 hGRH hp hne hinv (2 * m) (g m))
                  (primitiveHeightSeqUpperCorner hN2 hGRH hp hne hinv (g m))).filter
              (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
          dirichletLFunctionReciprocalZeroContribution x χ ρ)
      Filter.atTop
      (nhds
        (-((∑' j : ℕ,
                x⁻¹ ^ (2 * j + 1 + 1) / (((2 * j + 1 : ℕ) : ℝ) * (((2 * j + 1 : ℕ) : ℝ) + 1)) :
              ℝ) :
            ℂ))) := by
  have hi : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (of_decide_eq_true rfl : 0 < 2) (Nat.add_right_cancel h)
  have hs := (summable_reciprocal_inversePower_nat hx).comp_injective hi
  have ht :
    Filter.Tendsto
      (fun m =>
        -((∑ j ∈ Finset.range m,
                x⁻¹ ^ (2 * j + 1 + 1) / (((2 * j + 1 : ℕ) : ℝ) * (((2 * j + 1 : ℕ) : ℝ) + 1)) :
              ℝ) :
            ℂ))
      Filter.atTop
      (nhds
        (-((∑' j : ℕ,
                x⁻¹ ^ (2 * j + 1 + 1) / (((2 * j + 1 : ℕ) : ℝ) * (((2 * j + 1 : ℕ) : ℝ) + 1)) :
              ℝ) :
            ℂ))) := by
    simpa only [Complex.ofReal_neg, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto _).comp hs.hasSum.tendsto_sum_nat.neg
  exact
    ht.congr'
      (by
        filter_upwards [Filter.eventually_ge_atTop 1] with m hm
        exact
          (sum_odd_reciprocal_trivialZeros_primitiveRectangle_eq hN2 hGRH hp hne hinv ho x m (g m)
              hm).symm)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
