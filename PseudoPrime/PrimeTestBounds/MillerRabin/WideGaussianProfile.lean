/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeHighNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeTripleBounds

/-! # Relative Gaussian witnesses at the lower dual-scale entrance -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input bounds for a relative Gaussian witness from scale 200000000.
The fields certify the radius, fourth root and strict scalar margin. -/
structure WideGaussianProfile where
  C : ℝ
  T : ℝ
  a : ℝ
  v : ℝ
  entry : 200000000 ≤ T
  root : 36 / 100 ≤ a
  square : a ^ 2 ≤ C / (21 / 10)
  upper : C ≤ 290762661 / 1000000000
  fourth : 0 < v ∧ v ^ 2 ≤ T
  margin :
    38 <
      ((10971611 / 5000000) * a - 2 * (20115621 / 50000000) -
          (61 / 100) * (28794111 / 12500000) / v) *
        T

/-- The certified cutoff has the radius and fourth-root bounds needed by the Gaussian comparison. -/
theorem wideGaussian_roots (f : WideGaussianProfile) {L : ℝ} (hL : f.T ≤ L) :
    let r := Real.sqrt (f.C / (21 / 10) * L ^ 2)
    let s := Real.sqrt r
    f.a * L ≤ r ∧ 500 ≤ r ∧ 10 ≤ s ∧ s ≤ (61 / 100 : ℝ) * L / f.v := by
  let x := f.C / (21 / 10) * L ^ 2
  let r := Real.sqrt x
  have hL0 : 0 ≤ L := by linarith only [hL, f.entry]
  have ha : 0 ≤ f.a := by linarith only [f.root]
  have hx : 0 ≤ x := mul_nonneg ((sq_nonneg f.a).trans f.square) (sq_nonneg L)
  have hr : f.a * L ≤ r := by
    apply (Real.le_sqrt (mul_nonneg ha hL0) hx).mpr
    dsimp only [x]
    nlinarith only [mul_le_mul_of_nonneg_right f.square (sq_nonneg L)]
  have hr500 : 500 ≤ r := by
    have hh := mul_le_mul_of_nonneg_right f.root hL0
    nlinarith only [hr, hh, hL, f.entry]
  have hs10 : 10 ≤ Real.sqrt r := by
    apply (Real.le_sqrt (by norm_num only) (Real.sqrt_nonneg x)).mpr
    norm_num only
    exact (by linarith only [hr500])
  have hru : r ≤ (3721 / 10000 : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) hL0
    · dsimp only [x]
      nlinarith only [mul_le_mul_of_nonneg_right f.upper (sq_nonneg L)]
  have hsu : Real.sqrt r ≤ (61 / 100 : ℝ) * Real.sqrt L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) (Real.sqrt_nonneg L)
    · nlinarith only [hru, Real.sq_sqrt hL0]
  have hm := mul_le_mul_of_nonneg_right (f.fourth.2.trans hL) hL0
  have hrootL : Real.sqrt L ≤ L / f.v := by
    apply (le_div_iff₀ f.fourth.1).2
    have hsq := Real.sq_sqrt hL0
    have hpos := mul_nonneg (Real.sqrt_nonneg L) f.fourth.1.le
    nlinarith only [hsq, hm, hpos, hL0]
  have hmul := mul_le_mul_of_nonneg_left hrootL (by norm_num only : (0 : ℝ) ≤ 61 / 100)
  refine ⟨hr, hr500, hs10, ?_⟩
  change Real.sqrt r ≤ (61 / 100 : ℝ) * L / f.v
  simpa only [mul_div_assoc] using hsu.trans hmul

/-- The radius bounds control the signed prefix error at every covering scale. -/
theorem wideGaussian_error (f : WideGaussianProfile) {n : ℕ} {L : ℝ} (hL : f.T ≤ L)
    (hn : Real.log n ≤ L) :
    let r := Real.sqrt (f.C / (21 / 10) * L ^ 2)
    LLS.PaperStatements.gaussianPrefixError (489311 / 100000) n (r ^ 2) ≤
      (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + 4 + 273 / 1000 := by
  let r := Real.sqrt (f.C / (21 / 10) * L ^ 2)
  have hroots := wideGaussian_roots f hL
  change f.a * L ≤ r ∧ 500 ≤ r ∧ 10 ≤ Real.sqrt r ∧ Real.sqrt r ≤ (61 / 100 : ℝ) * L / f.v at hroots
  have hrpos : 0 < r := by linarith only [hroots.2.1]
  have hL0 : 0 ≤ L := by linarith only [hL, f.entry]
  have hroot := mul_le_mul_of_nonneg_right f.root hL0
  have hpole : (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log n + 4) / r) ≤ 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hrpos]
    linarith only [hroots.1, hroot, hL, f.entry, hn]
  have ht := gaussian1000_tail (show 100 ≤ r by linarith only [hroots.2.1])
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  change
    (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + (512 / 27) / r ^ 2 +
        (2129 / 2000) * (((7 / 6) * Real.log n + 4) / r) +
        (473 / 10) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤
      _
  linarith only [hpole, ht.1, ht.2]

/-- The profile margin contradicts the index-four Gaussian comparison with bounded errors. -/
theorem wideGaussian_false (f : WideGaussianProfile) {L : ℝ} (hL : f.T ≤ L) {r s A : ℝ}
    (hr : f.a * L ≤ r) (hr500 : 500 ≤ r) (hs10 : 10 ≤ s) (hs : s ≤ (61 / 100 : ℝ) * L / f.v)
    (hA : A ≤ (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + 4 + 273 / 1000)
    (hcmp :
      (10971611 / 5000000 : ℝ) * r ≤
        2 * (20115621 / 50000000 : ℝ) * L + (28794111 / 12500000 : ℝ) * s +
          4 *
            (21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * s) +
              1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
          13 +
          3 * A) :
    False := by
  have hspos : 0 < s := by linarith only [hs10]
  have hrpos : 0 < r := by linarith only [hr500]
  have hleft : 21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * s) ≤ 21 * (2129 / 2000 : ℝ) / 40 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hspos)).mpr
    nlinarith only [hs10]
  have hright : 1839 * (2129 / 2000 : ℝ) / (1000 * r) ≤ 1839 * (2129 / 2000 : ℝ) / 500000 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hrpos)).mpr
    nlinarith only [hr500]
  let d :=
    (10971611 / 5000000 : ℝ) * f.a - 2 * (20115621 / 50000000 : ℝ) -
      (61 / 100 : ℝ) * (28794111 / 12500000 : ℝ) / f.v
  have hmargin : 38 < d * f.T := f.margin
  have hd : 0 < d := by
    have hT : 0 < f.T := by linarith only [f.entry]
    by_contra hn
    have hnp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hT.le
    linarith only [hmargin, hnp]
  have hmul := mul_le_mul_of_nonneg_left hL hd.le
  have hbound : d * L ≤ (1869354731 / 50000000 : ℝ) := by
    dsimp only [d]
    simp only [div_eq_mul_inv] at hs ⊢
    nlinarith only [hcmp, hr, hs, hA, hleft, hright]
  linarith only [hmargin, hmul, hbound]

/-- Under GRH, an index-four subgroup with the stated conductor bound gives an actual
rejecting prime within the profile cutoff. -/
theorem wideGaussian_witness_four (f : WideGaussianProfile) {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : f.T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let x := (f.C / (21 / 10) * L ^ 2)
  let r := Real.sqrt x
  let s := Real.sqrt r
  let h := (2 / 5 : ℝ) / s
  have hroots := wideGaussian_roots f hL
  change f.a * L ≤ r ∧ 500 ≤ r ∧ 10 ≤ s ∧ s ≤ (61 / 100 : ℝ) * L / f.v at hroots
  have hrpos : 0 < r := by linarith only [hroots.2.1]
  have hspos : 0 < s := by linarith only [hroots.2.2.1]
  have hx0 : 0 ≤ x := mul_nonneg ((sq_nonneg f.a).trans f.square) (sq_nonneg L)
  have hr2 : r ^ 2 = x := Real.sq_sqrt hx0
  have hs2 : r = s ^ 2 := (Real.sq_sqrt hrpos.le).symm
  have hh : 0 < h := div_pos (by norm_num only) hspos
  have hh1 : h ≤ 1 / 2 := by
    apply (div_le_iff₀ hspos).mpr
    linarith only [hroots.2.2.1]
  have hr500 : (500 : ℝ) ≤ r := hroots.2.1
  have hx : 4 ≤ x := by nlinarith only [hr2, hr500]
  have hX : (50000 : ℝ) ≤ (21 / 10 : ℝ) * x := by nlinarith only [hr2, hr500]
  have hcut : (21 / 10 : ℝ) * x ≤ f.C * Real.log n ^ 2 := by
    dsimp only [x, L]
    exact le_of_eq (by ring)
  have hprefix :
    (489311 / 100000 : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 50000, Analysis.gaussianResolventMangoldtWeight j := by
    simpa only [Nat.floor_ofNat] using
      LLS.gaussian_prefix50000_seeded hGRH.riemann (le_refl (50000 : ℝ))
  apply
    gaussianRelative_witness hnOdd hnlarge H hHpass hGRH hprefix hh hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hX hcut
  intro hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  rw [← hr2, Real.sqrt_sq hrpos.le] at hcmp
  have hcmp' :
    (4 * (1 - h) *
            (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        (1 * r) ≤
      gaussianMRRefinedConductor * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / (1 * r)) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError (489311 / 100000) n (r ^ 2) := by
    simpa only [hindex, hi, Nat.reduceSub, Nat.cast_ofNat, one_mul] using hcmp
  have hscalar :=
    LLS.gaussianRelativeFour_scalar hspos hs2 (by norm_num only : (0 : ℝ) < 1)
      (by norm_num only : (0 : ℝ) < 2 / 5) (show h = (2 / 5 : ℝ) / s from rfl) hh1
      LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le Analysis.gaussian_endpoint_exp_le hC
      (by norm_num only [gaussianMRRefinedConductor]) hcmp'
  have hA := wideGaussian_error f hL (le_refl (Real.log n))
  apply wideGaussian_false f hL hroots.1 hroots.2.1 hroots.2.2.1 hroots.2.2.2 hA
  norm_num only [one_mul, gaussianMRRefinedConductor] at hscalar ⊢
  exact hscalar

/-- Under GRH, the uniform three-prime case gives a rejecting prime within the profile cutoff. -/
theorem wideGaussian_witness_triple (f : WideGaussianProfile) {n p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : f.T ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (f.C * Real.log n ^ 2) ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact wideGaussian_witness_four f hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- Under GRH, the squarefree uniform three-factor case gives a rejecting prime
within the profile cutoff. -/
theorem wideGaussian_witness_card (f : WideGaussianProfile) {n : ℕ} (hnOdd : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : f.T ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (f.C * Real.log n ^ 2) ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hc
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  exact
    wideGaussian_witness_triple f hp hq hr (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
