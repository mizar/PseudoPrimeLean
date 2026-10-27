/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Harmonic.Bounds
public import PseudoPrime.NumberTheory.TotientProductBounds
public import Mathlib.Tactic

/-! # Reciprocal sums over squarefree integers

Finite reciprocal-sum comparisons for squarefree integers and coprimality.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/--
Inputs: a cutoff `z` and a nonzero modulus `Q`.

Claim: the reciprocal sum over positive squarefree integers at most `z` is
bounded by the reciprocal sum over those also coprime to `Q`, multiplied by
`∏_{p ∣ Q} (1 + 1/p)`.

Proof: send each squarefree integer `m` to its quotient by `gcd m Q` and the
prime factors of that gcd. This map is injective, its first coordinate is
squarefree and coprime to `Q`, and the ambient product sum factors by
`Finset.prod_one_add`.

Role: converts the unrestricted squarefree reciprocal lower bound into a
lower bound for the range coprime to `Q`.
-/
theorem squarefree_reciprocal_sum_le_factor_mul_coprime_sum (z Q : ℕ) (hQ : Q ≠ 0) :
    (∑ m ∈ (Finset.range (z + 1)).filter Squarefree, 1 / (m : ℝ)) ≤
      (∑ n ∈ (Finset.range (z + 1)).filter (fun n : ℕ => Squarefree n ∧ Nat.Coprime n Q),
          1 / (n : ℝ)) *
        ∏ p ∈ Q.primeFactors, (1 + (p : ℝ)⁻¹) := by
  classical
  let A : Finset ℕ := (Finset.range (z + 1)).filter Squarefree
  let B : Finset ℕ := (Finset.range (z + 1)).filter (fun n : ℕ => Squarefree n ∧ Nat.Coprime n Q)
  let T : Finset (Finset ℕ) := Q.primeFactors.powerset
  let F : ℕ → ℕ × Finset ℕ := fun m => (m / Nat.gcd m Q, (Nat.gcd m Q).primeFactors)
  let w : ℕ × Finset ℕ → ℝ := fun x => (x.1 : ℝ)⁻¹ * ∏ p ∈ x.2, (p : ℝ)⁻¹
  have hFmem : ∀ m ∈ A, F m ∈ B ×ˢ T := by
    intro m hm
    have hmSq : Squarefree m := (Finset.mem_filter.mp hm).2
    have hdvdm : Nat.gcd m Q ∣ m := Nat.gcd_dvd_left m Q
    have hdvdQ : Nat.gcd m Q ∣ Q := Nat.gcd_dvd_right m Q
    have hdsq : Squarefree (Nat.gcd m Q) := hmSq.squarefree_of_dvd hdvdm
    have hnsq : Squarefree (m / Nat.gcd m Q) := hmSq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvdm)
    have hncop : Nat.Coprime (m / Nat.gcd m Q) Q := Nat.coprime_div_gcd_of_squarefree hmSq hQ
    have hmlt : m < z + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    have hnle : m / Nat.gcd m Q ≤ z := by
      exact le_trans (Nat.div_le_self m (Nat.gcd m Q)) (Nat.le_of_lt_succ hmlt)
    have hBn : m / Nat.gcd m Q ∈ B := by
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (lt_of_le_of_lt hnle (Nat.lt_succ_self z)), ⟨hnsq, hncop⟩⟩
    have hT : (Nat.gcd m Q).primeFactors ∈ T := by
      exact Finset.mem_powerset.mpr (Nat.primeFactors_mono hdvdQ hQ)
    exact Finset.mem_product.mpr (by simpa only [B, T, F] using And.intro hBn hT)
  have hFinj : Set.InjOn F A := by
    intro m hm m' hm' hpair
    have hmSq : Squarefree m := (Finset.mem_filter.mp hm).2
    have hm'Sq : Squarefree m' := (Finset.mem_filter.mp hm').2
    have hdSq : Squarefree (Nat.gcd m Q) := hmSq.squarefree_of_dvd (Nat.gcd_dvd_left m Q)
    have hd'Sq : Squarefree (Nat.gcd m' Q) := hm'Sq.squarefree_of_dvd (Nat.gcd_dvd_left m' Q)
    have hfirst : m / Nat.gcd m Q = m' / Nat.gcd m' Q := congrArg Prod.fst hpair
    have hsecond : (Nat.gcd m Q).primeFactors = (Nat.gcd m' Q).primeFactors :=
      congrArg Prod.snd hpair
    have hdiv : Nat.gcd m Q = Nat.gcd m' Q := by
      calc
        Nat.gcd m Q = ∏ p ∈ (Nat.gcd m Q).primeFactors, p :=
          (Nat.prod_primeFactors_of_squarefree hdSq).symm
        _ = ∏ p ∈ (Nat.gcd m' Q).primeFactors, p := by rw [hsecond]
        _ = Nat.gcd m' Q := Nat.prod_primeFactors_of_squarefree hd'Sq
    calc
      m = (m / Nat.gcd m Q) * Nat.gcd m Q := (Nat.div_mul_cancel (Nat.gcd_dvd_left m Q)).symm
      _ = (m' / Nat.gcd m' Q) * Nat.gcd m' Q := by rw [hfirst, hdiv]
      _ = m' := Nat.div_mul_cancel (Nat.gcd_dvd_left m' Q)
  have hweight : ∀ m ∈ A, w (F m) = 1 / (m : ℝ) := by
    intro m hm
    have hmSq : Squarefree m := (Finset.mem_filter.mp hm).2
    let d : ℕ := Nat.gcd m Q
    let n : ℕ := m / d
    have hdsq : Squarefree d := by
      simpa only [d] using hmSq.squarefree_of_dvd (Nat.gcd_dvd_left m Q)
    have hnSq : Squarefree n := by
      simpa only [n, d] using hmSq.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m Q))
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnSq.ne_zero
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdsq.ne_zero
    have hprod : (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
      calc
        (∏ p ∈ d.primeFactors, (p : ℝ)) = ((∏ p ∈ d.primeFactors, p : ℕ) : ℝ) :=
          (Nat.cast_prod _ _).symm
        _ = (d : ℝ) := congrArg (fun x : ℕ => (x : ℝ)) (Nat.prod_primeFactors_of_squarefree hdsq)
    have hfac : m = n * d := by
      simpa only [n, d] using (Nat.div_mul_cancel (Nat.gcd_dvd_left m Q)).symm
    dsimp only [w, F]
    change (n : ℝ)⁻¹ * ∏ p ∈ d.primeFactors, (p : ℝ)⁻¹ = 1 / (m : ℝ)
    rw [Finset.prod_inv_distrib, hprod, hfac, Nat.cast_mul]
    field_simp [hnR, hdR]
  have himage_subset : A.image F ⊆ B ×ˢ T := Finset.image_subset_iff.mpr hFmem
  have hsum_image : (∑ m ∈ A, 1 / (m : ℝ)) = ∑ x ∈ A.image F, w x := by
    calc
      _ = ∑ m ∈ A, w (F m) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact (hweight m hm).symm
      _ = ∑ x ∈ A.image F, w x := (Finset.sum_image hFinj).symm
  have hnonneg : ∀ x ∈ B ×ˢ T, x ∉ A.image F → 0 ≤ w x := by
    intro x hx _
    exact
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg x.1))
        (Finset.prod_nonneg fun p hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hsum_subset : (∑ x ∈ A.image F, w x) ≤ ∑ x ∈ B ×ˢ T, w x :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_subset hnonneg
  have hsum_product :
    (∑ x ∈ B ×ˢ T, w x) = (∑ n ∈ B, 1 / (n : ℝ)) * ∏ p ∈ Q.primeFactors, (1 + (p : ℝ)⁻¹) := by
    rw [Finset.sum_product]
    simp only [w]
    calc
      _ = ∑ n ∈ B, ((n : ℝ)⁻¹ * ∑ t ∈ T, ∏ p ∈ t, (p : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (Finset.mul_sum T (fun t => ∏ p ∈ t, (p : ℝ)⁻¹) ((n : ℝ)⁻¹)).symm
      _ = (∑ n ∈ B, 1 / (n : ℝ)) * (∑ t ∈ T, ∏ p ∈ t, (p : ℝ)⁻¹) := by
        rw [Finset.sum_mul]
        simp only [one_div]
      _ = (∑ n ∈ B, 1 / (n : ℝ)) * ∏ p ∈ Q.primeFactors, (1 + (p : ℝ)⁻¹) := by
        rw [Finset.prod_one_add]
  rw [hsum_image]
  exact le_trans hsum_subset (le_of_eq hsum_product)

/--
Inputs: a cutoff `z ≥ 1`.

Claim: the sum of reciprocal squares from `1` through `z` is at most `2`.

Proof: bound the tail after `1` by the integral estimate for inverse squares.

Role: controls the square factor in the squarefree reciprocal-sum estimate.
-/
theorem reciprocalSquareSum_Icc_le_two (z : ℕ) (hz : 1 ≤ z) :
    (∑ n ∈ Finset.Icc 1 z, ((n : ℝ) ^ 2)⁻¹) ≤ 2 := by
  have hset : Finset.Icc 1 z = insert 1 (Finset.Ioc 1 z) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hset, Finset.sum_insert]
  · have htail :=
      sum_Ioc_inv_sq_le_sub (α := ℝ) (by norm_num only : (1 : ℕ) ≠ 0) (by exact_mod_cast hz)
    have htail' : (∑ n ∈ Finset.Ioc 1 z, ((n : ℝ) ^ 2)⁻¹) ≤ 1 := by
      have hnonneg : 0 ≤ ((z : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg z)
      norm_num only at htail
      linarith only [htail, hnonneg]
    have hone : (((1 : ℕ) : ℝ) ^ 2)⁻¹ = 1 := by norm_num only
    rw [hone]
    linarith only [htail']
  · simp only [Finset.mem_Ioc, not_and]
    omega

/--
Inputs: a cutoff `z ≥ 1`.

Claim: the reciprocal sum over positive squarefree integers through `z` is at
least half the logarithm of `z + 1`.

Proof: write every positive integer uniquely as a square times a squarefree
integer, bound the reciprocal square sum by `2`, and compare the resulting
product with the harmonic sum.

Role: gives an explicit logarithmic lower bound for squarefree reciprocal sums.
-/
theorem squarefreeReciprocalSum_ge_log_div_two (z : ℕ) (hz : 1 ≤ z) :
    Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤
      ∑ n ∈ (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n), 1 / (n : ℝ) := by
  let B : Finset ℕ := Finset.Icc 1 z
  let D : Finset ℕ := (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n)
  have hDmem (a : ℕ) : a ∈ D ↔ 0 < a ∧ Squarefree a ∧ a ≤ z := by
    simp only [D, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨haRange, ⟨hpos, hsq⟩⟩
      exact ⟨hpos, hsq, by omega⟩
    · rintro ⟨hpos, hsq, ha⟩
      exact ⟨by omega, ⟨hpos, hsq⟩⟩
  let X := { n : ℕ // n ∈ B }
  let P (q : ℕ × ℕ) : ℝ := (((q.1 : ℝ) ^ 2)⁻¹) * (q.2 : ℝ)⁻¹
  have hdecomp (x : X) :
    ∃ q : ℕ × ℕ, 0 < q.1 ∧ 0 < q.2 ∧ q.1 ^ 2 * q.2 = x.val ∧ Squarefree q.2 := by
    have hxpos : 0 < x.val := by
      have hx := Finset.mem_Icc.mp x.property
      omega
    obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hxpos
    exact ⟨(b, a), hb, ha, hab, hsq⟩
  let e : X → ℕ × ℕ := fun x => Classical.choose (hdecomp x)
  have he (x : X) :
    0 < (e x).1 ∧ 0 < (e x).2 ∧ (e x).1 ^ 2 * (e x).2 = x.val ∧ Squarefree (e x).2 :=
    Classical.choose_spec (hdecomp x)
  have hinj : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    have hxrep := (he x).2.2.1
    have hyrep := (he y).2.2.1
    rw [hxy] at hxrep
    exact hxrep.symm.trans hyrep
  have himage : Finset.image e Finset.univ ⊆ B ×ˢ D := by
    intro q hq
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hq
    have hxB : 1 ≤ x.val ∧ x.val ≤ z := by simpa only [B, Finset.mem_Icc] using x.property
    have hb_le : (e x).1 ≤ x.val := by
      have hbSq : (e x).1 ≤ (e x).1 ^ 2 := by
        simpa only [pow_two] using (Nat.le_mul_of_pos_right (m := (e x).1) (e x).1 (he x).1)
      calc
        (e x).1 ≤ (e x).1 ^ 2 := hbSq
        _ ≤ (e x).1 ^ 2 * (e x).2 := Nat.le_mul_of_pos_right (m := (e x).2) ((e x).1 ^ 2) (he x).2.1
        _ = x.val := (he x).2.2.1
    have ha_le : (e x).2 ≤ x.val := by
      calc
        (e x).2 ≤ (e x).1 ^ 2 * (e x).2 :=
          Nat.le_mul_of_pos_left (n := (e x).1 ^ 2) (e x).2 (Nat.pow_pos (he x).1)
        _ = x.val := (he x).2.2.1
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (he x).1, le_trans hb_le hxB.2⟩
    · exact (hDmem (e x).2).2 ⟨he x |>.2.1, he x |>.2.2.2, le_trans ha_le hxB.2⟩
  have hterm (x : X) : 1 / (x.val : ℝ) ≤ P (e x) := by
    have hcast : (x.val : ℝ) = ((e x).1 : ℝ) ^ 2 * ((e x).2 : ℝ) := by
      exact_mod_cast (he x).2.2.1.symm
    rw [hcast]
    dsimp only [P]
    have hbR : 0 < ((e x).1 : ℝ) := by exact_mod_cast (he x).1
    have haR : 0 < ((e x).2 : ℝ) := by exact_mod_cast (he x).2.1
    have hbr : ((e x).1 : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hbR)
    have har : ((e x).2 : ℝ) ≠ 0 := ne_of_gt haR
    field_simp [hbr, har]
    norm_num only
  have hsumBound : (∑ x : X, 1 / (x.val : ℝ)) ≤ ∑ q ∈ B ×ˢ D, P q := by
    exact
      Finset.sum_le_sum_of_injOn e (fun x hx y hy hxy => hinj hxy) himage (fun x hx => hterm x)
        (fun q hq hnot => by
          dsimp only [P]
          exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _)))
  have hsumProduct : (∑ q ∈ B ×ˢ D, P q) = (∑ b ∈ B, ((b : ℝ) ^ 2)⁻¹) * (∑ a ∈ D, (a : ℝ)⁻¹) := by
    unfold P
    rw [Finset.sum_product]
    change (∑ b ∈ B, ∑ a ∈ D, (((b : ℝ) ^ 2)⁻¹) * (a : ℝ)⁻¹) = _
    rw [← Finset.sum_mul_sum]
  have hsource : (∑ x : X, 1 / (x.val : ℝ)) = ∑ n ∈ B, 1 / (n : ℝ) := by
    exact Finset.sum_coe_sort B (fun n => 1 / (n : ℝ))
  have hsqsum := reciprocalSquareSum_Icc_le_two z hz
  have hbound : (∑ n ∈ B, 1 / (n : ℝ)) ≤ 2 * (∑ a ∈ D, (a : ℝ)⁻¹) := by
    rw [hsource, hsumProduct] at hsumBound
    have hsqsum' : (∑ b ∈ B, ((b : ℝ) ^ 2)⁻¹) ≤ 2 := by simpa only [B] using hsqsum
    have hDnonneg : 0 ≤ ∑ a ∈ D, (a : ℝ)⁻¹ := by
      apply Finset.sum_nonneg
      intro a ha
      exact inv_nonneg.mpr (Nat.cast_nonneg a)
    exact le_trans hsumBound (mul_le_mul_of_nonneg_right hsqsum' hDnonneg)
  have hsumCast : (harmonic z : ℝ) = ∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    calc
      ((∑ n ∈ Finset.Icc 1 z, (n : ℚ)⁻¹ : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 z, (((n : ℚ)⁻¹ : ℚ) : ℝ) :=
        map_sum (algebraMap ℚ ℝ) (fun n : ℕ => (n : ℚ)⁻¹) (Finset.Icc 1 z)
      _ = ∑ n ∈ Finset.Icc 1 z, (n : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Rat.cast_inv]
        exact congrArg (fun x : ℝ => x⁻¹) (by norm_cast)
  have hlog : Real.log ((z + 1 : ℕ) : ℝ) ≤ ∑ n ∈ B, 1 / (n : ℝ) := by
    simpa only [B, one_div] using (le_trans (log_add_one_le_harmonic z) (le_of_eq hsumCast))
  change Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤ ∑ n ∈ D, 1 / (n : ℝ)
  have hfinal := le_trans hlog hbound
  have hDinv : (∑ a ∈ D, (a : ℝ)⁻¹) = ∑ n ∈ D, 1 / (n : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [one_div]
  rw [← hDinv]
  linarith only [hfinal]

/--
Inputs: a cutoff `z`, a positive modulus `Q`, and `z ≥ 1`.

Claim: the reciprocal sum over positive squarefree integers at most `z` and
coprime to `Q` is at least `φ(Q)/Q` times `log(z + 1)/2`.

Proof: compare the unrestricted squarefree sum with the coprime sum using the
gcd factorization, bound its Euler factor by `Q/φ(Q)`, and use the logarithmic
lower bound for the unrestricted sum.

Role: supplies a lower bound for the reciprocal sum with primes dividing `Q`
removed.
-/
theorem squarefree_coprime_reciprocal_sum_ge_totient_ratio_log_div_two (z Q : ℕ) (hQ : 0 < Q)
    (hz : 1 ≤ z) :
    (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) ≤
      ∑ n ∈ (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n ∧ Nat.Coprime n Q),
        1 / (n : ℝ) := by
  let A : Finset ℕ := (Finset.range (z + 1)).filter Squarefree
  let D : Finset ℕ := (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n)
  let B : Finset ℕ := (Finset.range (z + 1)).filter (fun n : ℕ => Squarefree n ∧ Nat.Coprime n Q)
  let E : Finset ℕ :=
    (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n ∧ Nat.Coprime n Q)
  have hAeq : A = D := by
    ext n
    simp only [A, D, Finset.mem_filter]
    constructor
    · rintro ⟨hn, hsq⟩
      exact ⟨hn, Nat.pos_of_ne_zero hsq.ne_zero, hsq⟩
    · rintro ⟨hn, _, hsq⟩
      exact ⟨hn, hsq⟩
  have hBeq : B = E := by
    ext n
    simp only [B, E, Finset.mem_filter]
    constructor
    · rintro ⟨hn, hsq, hcop⟩
      exact ⟨hn, Nat.pos_of_ne_zero hsq.ne_zero, hsq, hcop⟩
    · rintro ⟨hn, _, hsq, hcop⟩
      exact ⟨hn, hsq, hcop⟩
  let S := ∑ m ∈ A, 1 / (m : ℝ)
  let R := ∑ n ∈ B, 1 / (n : ℝ)
  let ratio : ℝ := (Q : ℝ) / (Nat.totient Q : ℝ)
  have hfull : Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤ S := by
    change Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤ ∑ n ∈ A, 1 / (n : ℝ)
    rw [hAeq]
    exact squarefreeReciprocalSum_ge_log_div_two z hz
  have hsumBound : S ≤ R * ∏ p ∈ Q.primeFactors, (1 + (p : ℝ)⁻¹) := by
    simpa only [S, R, A, B] using
      squarefree_reciprocal_sum_le_factor_mul_coprime_sum z Q (Nat.ne_of_gt hQ)
  have hRnonneg : 0 ≤ R := by
    dsimp only [R, B]
    exact Finset.sum_nonneg fun n hn => one_div_nonneg.mpr (Nat.cast_nonneg n)
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hphi : 0 < (Nat.totient Q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hQ
  have hprod : ∏ p ∈ Q.primeFactors, (1 + (p : ℝ)⁻¹) ≤ ratio := by
    simpa only [ratio] using
      PseudoPrime.NumberTheory.TotientProductBounds.primeFactor_one_add_inv_prod_le_div_totient hQ
  have hscaled : Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤ R * ratio := by
    calc
      _ ≤ S := hfull
      _ ≤ R * ∏ p ∈ Q.primeFactors, (1 + (p : ℝ)⁻¹) := hsumBound
      _ ≤ R * ratio := mul_le_mul_of_nonneg_left hprod hRnonneg
  have hmul := mul_le_mul_of_nonneg_left hscaled (div_nonneg (le_of_lt hphi) (le_of_lt hQR))
  have hcancel : (Nat.totient Q : ℝ) / (Q : ℝ) * (R * ratio) = R := by
    dsimp only [ratio]
    field_simp [ne_of_gt hQR, ne_of_gt hphi]
  calc
    (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) ≤
        (Nat.totient Q : ℝ) / (Q : ℝ) * (R * ratio) :=
      hmul
    _ = R := hcancel
    _ =
        ∑ n ∈ (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n ∧ Nat.Coprime n Q),
          1 / (n : ℝ) :=
      by
      dsimp only [R]
      rw [hBeq]

/--
Inputs: cutoffs `Z`, `Q` with `0 < Q` and `Q ≤ Z`.

Claim: the squarefree reciprocal-totient sum up to `⌊Z/Q⌋`, over terms
coprime to `Q`, weighted by `Q/φ(Q)`, is at least `log(Z/Q)/2`.

Proof: replace each reciprocal `1/r` in the preceding squarefree lower bound
by the larger `1/φ(r)`, then compare `Z/Q` with `⌊Z/Q⌋ + 1`.

Role: provides the `log(Z/Q)` gain in the pre-sifted large-sieve estimate.
-/
theorem squarefree_coprime_reciprocal_totient_sum_ge_log_div_two (z Q : ℕ) (hQ : 0 < Q)
    (hz : 1 ≤ z) :
    Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤
      (Q : ℝ) / (Nat.totient Q : ℝ) *
        ∑ r ∈ (Finset.range (z + 1)).filter (fun r : ℕ => 0 < r ∧ Squarefree r ∧ Nat.Coprime r Q),
          1 / (Nat.totient r : ℝ) := by
  let S : Finset ℕ :=
    (Finset.range (z + 1)).filter (fun r : ℕ => 0 < r ∧ Squarefree r ∧ Nat.Coprime r Q)
  have hbase :
    (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) ≤ ∑ r ∈ S, 1 / (r : ℝ) := by
    simpa only [S] using squarefree_coprime_reciprocal_sum_ge_totient_ratio_log_div_two z Q hQ hz
  have hsum : ∑ r ∈ S, 1 / (r : ℝ) ≤ ∑ r ∈ S, 1 / (Nat.totient r : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    have hrpos : 0 < r := (Finset.mem_filter.mp hr).2.1
    have hphi : 0 < Nat.totient r := Nat.totient_pos.mpr hrpos
    have hphi_le : Nat.totient r ≤ r := Nat.totient_le r
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hrpos
    have hphiR : 0 < (Nat.totient r : ℝ) := by exact_mod_cast hphi
    have hphi_leR : (Nat.totient r : ℝ) ≤ (r : ℝ) := by exact_mod_cast hphi_le
    exact (div_le_div_iff₀ hrR hphiR).2 (by simpa only [one_mul] using hphi_leR)
  have hfac : 0 < (Q : ℝ) / (Nat.totient Q : ℝ) := by
    exact div_pos (by exact_mod_cast hQ) (by exact_mod_cast Nat.totient_pos.mpr hQ)
  have hmul := mul_le_mul_of_nonneg_left (le_trans hbase hsum) hfac.le
  have hQposR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hphiQposR : 0 < (Nat.totient Q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hQ
  have hcancel :
    (Q : ℝ) / (Nat.totient Q : ℝ) *
        ((Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2)) =
      Real.log ((z + 1 : ℕ) : ℝ) / 2 := by
    field_simp [ne_of_gt hQposR, ne_of_gt hphiQposR]
  calc
    Real.log ((z + 1 : ℕ) : ℝ) / 2 =
        (Q : ℝ) / (Nat.totient Q : ℝ) *
          ((Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2)) :=
      hcancel.symm
    _ ≤ (Q : ℝ) / (Nat.totient Q : ℝ) * ∑ r ∈ S, 1 / (Nat.totient r : ℝ) := hmul
    _ = _ := by rfl

theorem squarefree_coprime_reciprocal_totient_sum_ge_log_ratio_div_two (Z Q : ℕ) (hQ : 0 < Q)
    (hQZ : Q ≤ Z) :
    Real.log ((Z : ℝ) / (Q : ℝ)) / 2 ≤
      (Q : ℝ) / (Nat.totient Q : ℝ) *
        ∑
          r ∈
            (Finset.range (Z / Q + 1)).filter (fun r : ℕ => 0 < r ∧ Squarefree r ∧ Nat.Coprime r Q),
          1 / (Nat.totient r : ℝ) := by
  have hz : 1 ≤ Z / Q := (Nat.one_le_div_iff hQ).2 hQZ
  have hbase := squarefree_coprime_reciprocal_totient_sum_ge_log_div_two (Z / Q) Q hQ hz
  have hQposR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hZposR : 0 < (Z : ℝ) := by exact_mod_cast (lt_of_lt_of_le hQ hQZ)
  have hdivNat : Z < (Z / Q + 1) * Q := by
    exact (Nat.div_lt_iff_lt_mul hQ).mp (Nat.lt_succ_self (Z / Q))
  have hdivR : (Z : ℝ) < ((Z / Q + 1 : ℕ) : ℝ) * (Q : ℝ) := by exact_mod_cast hdivNat
  have hratio : (Z : ℝ) / (Q : ℝ) < ((Z / Q + 1 : ℕ) : ℝ) := (div_lt_iff₀ hQposR).2 hdivR
  have hlog : Real.log ((Z : ℝ) / (Q : ℝ)) ≤ Real.log ((Z / Q + 1 : ℕ) : ℝ) :=
    Real.log_le_log (div_pos hZposR hQposR) hratio.le
  have hhalf : Real.log ((Z : ℝ) / (Q : ℝ)) / 2 ≤ Real.log ((Z / Q + 1 : ℕ) : ℝ) / 2 :=
    div_le_div_of_nonneg_right hlog (by norm_num only)
  exact le_trans hhalf hbase

end PseudoPrime.AnalyticNumberTheory.Arithmetic
