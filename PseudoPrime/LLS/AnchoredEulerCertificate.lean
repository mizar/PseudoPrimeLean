/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AnchoredEulerPrefixClosedForm
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates

/-! # Rational certificates for finite anchored Euler constants -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For a positive anchor, lower power and logarithmic sums, upper Chebyshev and
smoothed sums, an upper primitive and upper negative power imply the displayed
lower bound for the actual anchor constant. Nonnegativity controls the signed product.
This is the aggregate interface for compact finite certificates. -/
theorem anchoredEulerConstant_ge_of_enclosures {a P U V S H R : ℝ} (ha : 0 < a)
    (hP : P ≤ ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-5 / 4 : ℝ))
    (hU : Chebyshev.psi a ≤ U) (hV : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a ≤ V)
    (hS :
      S ≤
        ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
          (3 / 4 : ℝ) * Real.log m * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ (11 / 4 : ℝ))
    (hH : anchoredEulerTailPrimitive a ≤ H) (hR : a ^ (-5 / 4 : ℝ) ≤ R) :
    P - H - R * (U + (5 / 4 : ℝ) * V) + S ≤ anchoredEulerConstant a := by
  have hA : 0 ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a :=
    Finset.sum_nonneg
      (fun n hn ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_nonneg ha (Finset.mem_Ioc.mp hn).1
          (Finset.mem_Ioc.mp hn).2)
  have hb :
    Chebyshev.psi a + (5 / 4 : ℝ) * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a ≤
      U + (5 / 4 : ℝ) * V := by
    linarith only [hU, hV]
  have hm :=
    mul_le_mul hR hb
      (by linarith only [Chebyshev.psi_nonneg a, hA] :
        0 ≤
          Chebyshev.psi a + (5 / 4 : ℝ) * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a)
      ((Real.rpow_nonneg ha.le (-5 / 4 : ℝ)).trans hR)
  dsimp only [anchoredEulerConstant]
  linarith only [hP, hS, hH, hm]

/-- For a prime power n=p^k below a positive anchor, rational-type bounds on log p
and two negative powers give four lower or upper term enclosures. Use the exact
Mangoldt prime-power identity and logarithmic monotonicity. This supplies the
individual terms of the power, Chebyshev, smoothed and logarithmic prefixes. -/
theorem anchor_primePower_term_enclosures {p k n : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hn : n = p ^ k)
    {a lo hi v w ell : ℝ} (hna : (n : ℝ) ≤ a) (hlo : 0 ≤ lo) (hl : lo ≤ Real.log p)
    (hu : Real.log p ≤ hi) (hv0 : 0 ≤ v) (hv : v ≤ (n : ℝ) ^ (-5 / 4 : ℝ)) (hw0 : 0 ≤ w)
    (hw : w ≤ (n : ℝ) ^ (-11 / 4 : ℝ)) (hell : Real.log a ≤ ell) :
    lo * v ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-5 / 4 : ℝ) ∧
      ArithmeticFunction.vonMangoldt n ≤ hi ∧
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm a n ≤ hi * (ell - (k : ℝ) * lo) ∧
      (3 / 4 : ℝ) * (k : ℝ) * lo ^ 2 * w ≤
        (3 / 4 : ℝ) * Real.log n * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (11 / 4 : ℝ) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (hn ▸ pow_pos hp.pos k)
  have ha := hn0.trans_le hna
  have hΛ : ArithmeticFunction.vonMangoldt n = Real.log p := by
    rw [hn, ArithmeticFunction.vonMangoldt_apply_pow hk,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log n = (k : ℝ) * Real.log p := by rw [hn, Nat.cast_pow, Real.log_pow]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hnlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hnl : (k : ℝ) * lo ≤ Real.log n := by
    rw [hlog]
    exact mul_le_mul_of_nonneg_left hl hk0
  have hr0 : 0 ≤ Real.log (a / n) :=
    Real.log_nonneg ((le_div_iff₀ hn0).mpr (by simpa only [one_mul] using hna))
  have hr : Real.log (a / n) ≤ ell - (k : ℝ) * lo := by
    rw [Real.log_div ha.ne' hn0.ne']
    linarith only [hell, hnl]
  have hP := mul_le_mul hl hv hv0 hp0
  have hA := mul_le_mul hu hr hr0 (hp0.trans hu)
  have hcoef := mul_le_mul hnl hl hlo hnlog
  have hcoef' := mul_le_mul_of_nonneg_left hcoef (by norm_num only : (0 : ℝ) ≤ 3 / 4)
  have hS :=
    mul_le_mul hcoef' hw hw0
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) (mul_nonneg hnlog hp0))
  rw [hΛ]
  refine ⟨hP, hu, ?_, ?_⟩
  · dsimp only [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm]
    rw [hΛ]
    exact hA
  · rw [neg_div, Real.rpow_neg (Nat.cast_nonneg n)] at hS
    simp only [div_eq_mul_inv] at hS ⊢
    nlinarith only [hS]

/-- One rational certificate row for a prime power. Fields p,k describe its base
and exponent; lo,hi enclose log p; v,w are lower endpoints for n^(-5/4),n^(-11/4).
No invariant is built into the structure. The checker validates primality, exponent,
index identity and all scalar inequalities before the row is used analytically. -/
structure AnchorEulerAtom where
  p : ℕ
  k : ℕ
  lo : ℚ
  hi : ℚ
  v : ℚ
  w : ℚ
  deriving Inhabited, DecidableEq

/-- The exact Boolean check for an atom at index n with a chosen Taylor length.
It checks prime-power data, nonnegative lower endpoints, the logarithm interval and
two fourth-power comparisons. A successful result supplies the analytic term bounds. -/
def anchorEulerAtomCheck (terms n : ℕ) (r : AnchorEulerAtom) : Bool :=
  decide (r.p.Prime ∧ r.k ≠ 0 ∧ r.p ^ r.k = n ∧ 0 ≤ r.lo ∧ 0 ≤ r.v ∧ 0 ≤ r.w) &&
    (Analysis.rationalLogIntervalCheck r.p (Nat.log2 r.p + 1) terms r.lo r.hi &&
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck n r.v 1 5 4 &&
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck n r.w 1 11 4))

/-- The rational lower power-prefix term lo*v at a prime-power index, and zero
otherwise. The conditional lets missing nonprime-power rows use the default atom.
Soundness is provided by the common atom-check theorem. -/
def anchorEulerAtomP (n : ℕ) (r : AnchorEulerAtom) : ℚ :=
  if IsPrimePow n then r.lo * r.v else 0

/-- The rational upper Mangoldt term hi at a prime-power index, and zero otherwise.
This is summed to bound the finite Chebyshev value in the anchor boundary. -/
def anchorEulerAtomPsi (n : ℕ) (r : AnchorEulerAtom) : ℚ :=
  if IsPrimePow n then r.hi else 0

/-- The rational upper smoothed term hi*(ell-k*lo) at a prime-power index, and zero
otherwise. The input ell bounds the anchor logarithm. This bounds the negative
smoothed boundary without losing its finite arithmetic structure. -/
def anchorEulerAtomA (ell : ℚ) (n : ℕ) (r : AnchorEulerAtom) : ℚ :=
  if IsPrimePow n then r.hi * (ell - (r.k : ℚ) * r.lo) else 0

/-- The rational lower logarithmic-prefix term (3/4)k*lo^2*w at a prime power,
and zero otherwise. This retains the positive second part of the paired Euler weight. -/
def anchorEulerAtomS (n : ℕ) (r : AnchorEulerAtom) : ℚ :=
  if IsPrimePow n then (3 / 4 : ℚ) * (r.k : ℚ) * r.lo ^ 2 * r.w else 0

/-- For an index below the anchor and a valid anchor-log upper endpoint, successful
prime-power row checks imply all four real term enclosures. Handle nonprime powers
by their zero Mangoldt value. This reflects exact rational checks into real inequalities. -/
theorem anchorEulerAtomCheck_sound {terms n : ℕ} {r : AnchorEulerAtom} {a : ℝ} {ell : ℚ}
    (hna : (n : ℝ) ≤ a) (hell : Real.log a ≤ (ell : ℝ))
    (hc : IsPrimePow n → anchorEulerAtomCheck terms n r = true) :
    (anchorEulerAtomP n r : ℝ) ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-5 / 4 : ℝ) ∧
      ArithmeticFunction.vonMangoldt n ≤ (anchorEulerAtomPsi n r : ℝ) ∧
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm a n ≤ (anchorEulerAtomA ell n r : ℝ) ∧
      (anchorEulerAtomS n r : ℝ) ≤
        (3 / 4 : ℝ) * Real.log n * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (11 / 4 : ℝ) := by
  by_cases hn : IsPrimePow n
  · have h := hc hn
    simp only [anchorEulerAtomCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := Analysis.rationalLogIntervalCheck_sound h.2.1
    have hv := AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound h.2.2.1
    have hw := AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound h.2.2.2
    simp only [Rat.cast_natCast] at hl hv hw
    norm_num only at hv hw
    have he :=
      anchor_primePower_term_enclosures h.1.1 h.1.2.1 h.1.2.2.1.symm hna
        (Rat.cast_nonneg.mpr h.1.2.2.2.1) hl.1 hl.2 (Rat.cast_nonneg.mpr h.1.2.2.2.2.1)
        (by simpa only [neg_div] using hv.1) (Rat.cast_nonneg.mpr h.1.2.2.2.2.2)
        (by simpa only [neg_div] using hw.1) hell
    simpa only [anchorEulerAtomP, anchorEulerAtomPsi, anchorEulerAtomA, anchorEulerAtomS,
      ite_eq_left hn, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_pow] using he
  · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    simp only [anchorEulerAtomP, anchorEulerAtomPsi, anchorEulerAtomA, anchorEulerAtomS,
      ite_eq_right hn, Rat.cast_zero, hz, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm,
      zero_mul, mul_zero, zero_div, le_refl, and_self]

/-- For a positive anchor and logarithm and negative-power enclosures, the displayed
rational expression bounds the primitive above. Keep the negative coefficient's
lower endpoint and use upper endpoints for the positive products. This supplies
the primitive contribution in the finite constant certificate. -/
theorem anchoredEulerTailPrimitive_le_of_enclosures {a l u v ell : ℝ} (ha : 0 < a)
    (hl : l ≤ a ^ (-1 / 4 : ℝ)) (hu : a ^ (-3 / 4 : ℝ) ≤ u) (hv : a ^ (-5 / 4 : ℝ) ≤ v)
    (hell : Real.log a ≤ ell) (hlog : 0 ≤ Real.log a) :
    anchoredEulerTailPrimitive a ≤
      -(25 / 4 : ℝ) * l + (5 / 48 : ℝ) * u + ((1839 / 800 : ℝ) * ell + 6303 / 2000) * v := by
  have h1 := mul_le_mul_of_nonpos_left hl (by norm_num only : -(25 / 4 : ℝ) ≤ 0)
  have h2 := mul_le_mul_of_nonneg_left hu (by norm_num only : (0 : ℝ) ≤ 5 / 48)
  have hc : (1839 / 800 : ℝ) * Real.log a + 6303 / 2000 ≤ (1839 / 800 : ℝ) * ell + 6303 / 2000 := by
    linarith only [hell]
  have h3 :=
    mul_le_mul hc hv (Real.rpow_nonneg ha.le (-5 / 4 : ℝ))
      (by linarith only [hlog, hell] : 0 ≤ (1839 / 800 : ℝ) * ell + 6303 / 2000)
  dsimp only [anchoredEulerTailPrimitive]
  linarith only [h1, h2, h3]

/-- The rational aggregate lower bound assembled from all indices through N.
Inputs are the logarithm upper endpoint, one lower and two upper anchor-power
endpoints, and indexed atom data. Its sign choices match the finite anchor constant. -/
def anchorEulerRationalLower (N : ℕ) (ell l u v : ℚ) (r : ℕ → AnchorEulerAtom) : ℚ :=
  (∑ n ∈ Finset.Ioc 0 N, anchorEulerAtomP n (r n)) -
      (-(25 / 4 : ℚ) * l + (5 / 48 : ℚ) * u + ((1839 / 800 : ℚ) * ell + 6303 / 2000) * v) -
      v *
        ((∑ n ∈ Finset.Ioc 0 N, anchorEulerAtomPsi n (r n)) +
          (5 / 4 : ℚ) * ∑ n ∈ Finset.Ioc 0 N, anchorEulerAtomA ell n (r n)) +
    ∑ n ∈ Finset.Ioc 0 N, anchorEulerAtomS n (r n)

/-- For a positive integer anchor, valid scalar endpoints and successful atom checks,
the rational aggregate is below the actual finite anchor constant. Sum the four term
bounds and apply the signed aggregate inequality. This is independent of RH and
allows the concrete certificate data to stay small. -/
theorem anchorEulerRationalLower_le {N terms : ℕ} (hN : 0 < N) (ell l u v : ℚ)
    (r : ℕ → AnchorEulerAtom) (hell : Real.log (N : ℝ) ≤ (ell : ℝ))
    (hl : (l : ℝ) ≤ (N : ℝ) ^ (-1 / 4 : ℝ)) (hu : (N : ℝ) ^ (-3 / 4 : ℝ) ≤ (u : ℝ))
    (hv : (N : ℝ) ^ (-5 / 4 : ℝ) ≤ (v : ℝ))
    (hc : ∀ n ∈ Finset.Ioc 0 N, IsPrimePow n → anchorEulerAtomCheck terms n (r n) = true) :
    (anchorEulerRationalLower N ell l u v r : ℝ) ≤ anchoredEulerConstant N := by
  have hn0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hrows (n : ℕ) (hn : n ∈ Finset.Ioc 0 N) :=
    anchorEulerAtomCheck_sound (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2) hell (hc n hn)
  have hP :
    ((∑ n ∈ Finset.Ioc 0 N, anchorEulerAtomP n (r n) : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊(N : ℝ)⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-5 / 4 : ℝ) := by
    rw [Nat.floor_natCast, Rat.cast_sum]
    exact Finset.sum_le_sum (fun n hn ↦ (hrows n hn).1)
  have hU :
    Chebyshev.psi (N : ℝ) ≤ ((∑ n ∈ Finset.Ioc 0 N, anchorEulerAtomPsi n (r n) : ℚ) : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Rat.cast_sum, ←
      Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le N), ArithmeticFunction.map_zero, add_zero]
    exact Finset.sum_le_sum (fun n hn ↦ (hrows n hn).2.1)
  have hV :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (N : ℝ) ≤
      ((∑ n ∈ Finset.Ioc 0 N, anchorEulerAtomA ell n (r n) : ℚ) : ℝ) := by
    rw [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum, Nat.floor_natCast, Rat.cast_sum]
    exact Finset.sum_le_sum (fun n hn ↦ (hrows n hn).2.2.1)
  have hS :
    ((∑ n ∈ Finset.Ioc 0 N, anchorEulerAtomS n (r n) : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊(N : ℝ)⌋₊,
        (3 / 4 : ℝ) * Real.log m * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ (11 / 4 : ℝ) := by
    rw [Nat.floor_natCast, Rat.cast_sum]
    exact Finset.sum_le_sum (fun n hn ↦ (hrows n hn).2.2.2)
  have hH :=
    anchoredEulerTailPrimitive_le_of_enclosures hn0 hl hu hv hell (Real.log_natCast_nonneg N)
  have hb := anchoredEulerConstant_ge_of_enclosures hn0 hP hU hV hS hH hv
  simpa only [anchorEulerRationalLower, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_neg] using hb

end PseudoPrime.LLS
