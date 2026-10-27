/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.AffineProductFermatKernel
public import PseudoPrime.PrimeTestBounds.MillerRabin.ProductKernelAsymptoticBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteKernelBaseBounds

/-! # Unconditional MR bounds on affine cofactor progressions -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- SmallAffineCofactor n tau means n=p(k(p-1)+r+1), with p prime,
k unrestricted, and 0<r<=p^tau. It controls the local kernel through the
offset r, allowing arbitrarily large cofactors. Used in uniform MR bounds. -/
def SmallAffineCofactor (n : ℕ) (τ : ℝ) : Prop :=
  ∃ p k r : ℕ, p.Prime ∧ n = p * (k * (p - 1) + r + 1) ∧ 0 < r ∧ (r : ℝ) ≤ (p : ℝ) ^ τ

/-- A small positive affine offset gives a prime divisor with local kernel
at most p^tau. Apply the exact affine gcd identity and cast its bound.
Neither the multiplier nor cofactor primality is restricted. -/
theorem SmallAffineCofactor.small_kernel {n : ℕ} {τ : ℝ} (h : SmallAffineCofactor n τ) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ τ := by
  obtain ⟨p, k, r, hp, rfl, hr, hb⟩ := h
  exact
    ⟨p, hp, dvd_mul_right _ _,
      (Nat.cast_le.mpr (NumberTheory.gcd_predecessor_affine_product_le hp.pos hr)).trans hb⟩

/-- The previous small-cofactor or small-gap family is included in the
affine family. Choose multiplier zero or one and offset m-1 or m-p.
This verifies that the new arithmetic condition extends the old one. -/
theorem SmallCofactorOrGap.smallAffineCofactor {n : ℕ} {τ : ℝ} (h : SmallCofactorOrGap n τ) :
    SmallAffineCofactor n τ := by
  obtain ⟨p, m, hp, rfl, hs | hg⟩ := h
  · refine ⟨p, 0, m - 1, hp, ?_, Nat.sub_pos_of_lt hs.1, ?_⟩
    · rw [zero_mul, zero_add, Nat.sub_add_cancel (Nat.one_le_of_lt hs.1)]
    · exact (Nat.cast_le.mpr (Nat.sub_le m 1)).trans hs.2
  · refine ⟨p, 1, m - p, hp, ?_, Nat.sub_pos_of_lt hg.1, hg.2⟩
    rw [one_mul]
    have he : p - 1 + (m - p) + 1 = m := by
      nlinarith only [Nat.sub_add_cancel hp.pos, Nat.sub_add_cancel hg.1.le]
    rw [he]

/-- For fixed 0<tau<1 and A>1/(1-tau), sufficiently large odd n>1
in the affine family have least prime MR witness at most log(n)^A.
Apply the proved small-kernel theorem. Its threshold is uniform in k. -/
theorem eventually_exists_least_prime_witness_of_small_affine_cofactor {τ A : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ < 1) (hA : 1 / (1 - τ) < A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < n →
        Odd n →
        SmallAffineCofactor n τ →
        ∃ q : ℕ,
          q.Prime ∧
            ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
            (q : ℝ) ≤ (Real.log n) ^ A ∧
            ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → q ≤ r := by
  apply (eventually_exists_least_prime_witness_of_prime_small_kernel hτ0 hτ1 hA).mono
  intro n h hn ho hf
  exact h hn ho hf.small_kernel

/-- If A<2, the same affine-family bound is eventually strictly below
log(n)^2. Keep the least witness and compare real exponents at log(n)>1.
This transfers the strict analytic saving to arbitrary affine multipliers. -/
theorem eventually_exists_least_prime_witness_strict_of_small_affine_cofactor {τ A : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hA : 1 / (1 - τ) < A) (hA2 : A < 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < n →
        Odd n →
        SmallAffineCofactor n τ →
        ∃ q : ℕ,
          q.Prime ∧
            ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
            (q : ℝ) ≤ (Real.log n) ^ A ∧
            (q : ℝ) < (Real.log n) ^ 2 ∧
            ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → q ≤ r := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_exists_least_prime_witness_of_small_affine_cofactor hτ0 hτ1 hA,
    ht.eventually_gt_atTop 1] with n h hL hn ho hf
  obtain ⟨q, hq, hfail, hb, hleast⟩ := h hn ho hf
  have hs : (Real.log n) ^ A < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_lt_rpow_of_exponent_lt hL hA2
  exact ⟨q, hq, hfail, hb, hb.trans_lt hs, hleast⟩

/-- In an odd affine product, 1<b<p and b^r-1<p force MR rejection
when r>0. Use the offset as a multiple of the exact local kernel.
This pointwise theorem supplies finite small bases without a cutoff. -/
theorem not_strongMillerRabinPass_of_affine_power_bound {p k r b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Odd (k * (p - 1) + r + 1)) (hb : 1 < b) (hbp : b < p) (hr : 0 < r) (hs : b ^ r - 1 < p) :
    ¬PrimeTest.StrongMillerRabinPass (p * (k * (p - 1) + r + 1))
        (b : ZMod (p * (k * (p - 1) + r + 1))) := by
  have hn : 1 < p * (k * (p - 1) + r + 1) :=
    hp.one_lt.trans_le (Nat.le_mul_of_pos_right p (Nat.succ_pos _))
  exact
    not_strongMillerRabinPass_of_local_power_bound hn ((hp.odd_of_ne_two hp2).mul hm) hp
      (dvd_mul_right _ _) hb hbp hr (NumberTheory.gcd_predecessor_affine_product_dvd hp.pos) hs

/-- A positive small remainder of m-1 modulo p-1 supplies the affine
representation by Euclidean division. This is a directly computable
arithmetic criterion for the uniform affine-family witness theorem. -/
theorem smallAffineCofactor_of_remainder {p m : ℕ} {τ : ℝ} (hp : p.Prime) (hm : 0 < m)
    (hr : 0 < (m - 1) % (p - 1)) (hb : (((m - 1) % (p - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ τ) :
    SmallAffineCofactor (p * m) τ := by
  refine ⟨p, (m - 1) / (p - 1), (m - 1) % (p - 1), hp, ?_, hr, hb⟩
  have he : (m - 1) / (p - 1) * (p - 1) + (m - 1) % (p - 1) + 1 = m := by
    nlinarith only [Nat.mod_add_div (m - 1) (p - 1), Nat.sub_add_cancel hm]
  rw [he]

/-- For fixed 0<tau<1/2, the affine family admits a fixed exponent A<2
and an eventual least-prime MR bound strictly below log(n)^2. Choose A
between 1/(1-tau) and two. The unrestricted multiplier is uniform. -/
theorem exists_subquadratic_exponent_of_small_affine_cofactor {τ : ℝ} (hτ0 : 0 < τ)
    (hτhalf : τ < 1 / 2) :
    ∃ A : ℝ,
      0 < A ∧
        A < 2 ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          1 < n →
            Odd n →
            SmallAffineCofactor n τ →
            ∃ q : ℕ,
              q.Prime ∧
                ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
                (q : ℝ) ≤ (Real.log n) ^ A ∧
                (q : ℝ) < (Real.log n) ^ 2 ∧
                ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → q ≤ r := by
  have hτ1 : τ < 1 := lt_trans hτhalf (by norm_num only)
  have hd : 0 < 1 - τ := sub_pos.mpr hτ1
  have hb : 1 / (1 - τ) < (2 : ℝ) := by
    apply (div_lt_iff₀ hd).mpr
    linarith only [hτhalf]
  obtain ⟨A, hA, hA2⟩ := exists_between hb
  exact
    ⟨A, (div_pos zero_lt_one hd).trans hA, hA2,
      eventually_exists_least_prime_witness_strict_of_small_affine_cofactor hτ0 hτ1 hA hA2⟩

/-- For every prime p>3 and every natural k, the least prime MR witness
of p(k(p-1)+3) is two. The local kernel divides two, and 2^2-1=3<p.
Parity follows from p odd; cofactor primality and GRH are unnecessary. -/
theorem two_is_least_prime_witness_affine_add_three {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (k : ℕ) :
    Nat.Prime 2 ∧
      ¬PrimeTest.StrongMillerRabinPass (p * (k * (p - 1) + 3)) (2 : ZMod (p * (k * (p - 1) + 3))) ∧
      ∀ q : ℕ,
        q.Prime →
          ¬PrimeTest.StrongMillerRabinPass (p * (k * (p - 1) + 3))
              (q : ZMod (p * (k * (p - 1) + 3))) →
          2 ≤ q := by
  have hp2 : p ≠ 2 := ne_of_gt ((by decide : 2 < 3).trans hp3)
  have he : Even (p - 1) := Nat.Odd.sub_odd (hp.odd_of_ne_two hp2) (by decide : Odd (1 : ℕ))
  have hm : Odd (k * (p - 1) + 2 + 1) := by
    simpa only [Nat.add_assoc, show (2 : ℕ) + 1 = 3 by rfl] using
      (he.mul_left k).add_odd (by decide : Odd (3 : ℕ))
  have hf :=
    not_strongMillerRabinPass_of_affine_power_bound hp hp2 hm (by decide : 1 < 2)
      ((by decide : 2 < 3).trans hp3) (by decide : 0 < 2) (show (2 : ℕ) ^ 2 - 1 < p from hp3)
  refine ⟨Nat.prime_two, ?_, fun q hq _ ↦ hq.two_le⟩
  simpa only [Nat.add_assoc, show (2 : ℕ) + 1 = 3 by rfl, Nat.cast_ofNat] using hf

end PseudoPrime.PrimeTestBounds.MillerRabin
