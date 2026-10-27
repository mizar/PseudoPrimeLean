/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.PositiveCongruenceRatios
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Divisor counting for rational quotient sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive first numerator and denominator and two reduced natural fractions,
the crossed products remaining after canceling the two gcds are coprime.
Combine the four coprimality relations inherited from reduction and gcd cancellation. -/
theorem coprime_cross_after_gcd {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hcd : c.Coprime d) :
    ((a / a.gcd c) * (d / b.gcd d)).Coprime ((c / a.gcd c) * (b / b.gcd d)) := by
  have hac := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left c ha)
  have hbd := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left d hb)
  have hab' :=
    Nat.Coprime.of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left a c))
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left b d)) hab
  have hdc' :=
    Nat.Coprime.of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right b d))
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a c)) hcd.symm
  exact (hac.mul_right hab').mul_left (hdc'.mul_right hbd.symm)

/-- For positive a,b,c,d, cancel gcd(a,c) and gcd(b,d) in the quotient (a/b)/(c/d).
Write all four natural factors as their gcd times cofactor and cancel nonzero rational factors. -/
theorem quotient_gcd_reduction {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ((a : ℚ) / b) / ((c : ℚ) / d) =
      (((a / a.gcd c) * (d / b.gcd d) : ℕ) : ℚ) / (((c / a.gcd c) * (b / b.gcd d) : ℕ) : ℚ) := by
  have hg : 0 < a.gcd c := Nat.gcd_pos_of_pos_left c ha
  have hh : 0 < b.gcd d := Nat.gcd_pos_of_pos_left d hb
  have ha0 : 0 < a / a.gcd c := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a c)) hg
  have hb0 : 0 < b / b.gcd d := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_left b d)) hh
  have hc0 : 0 < c / a.gcd c := Nat.div_pos (Nat.le_of_dvd hc (Nat.gcd_dvd_right a c)) hg
  have hd0 : 0 < d / b.gcd d := Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_right b d)) hh
  have han : a / a.gcd c * a.gcd c = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a c)
  have hbn : b / b.gcd d * b.gcd d = b := Nat.div_mul_cancel (Nat.gcd_dvd_left b d)
  have hcn : c / a.gcd c * a.gcd c = c := Nat.div_mul_cancel (Nat.gcd_dvd_right a c)
  have hdn : d / b.gcd d * b.gcd d = d := Nat.div_mul_cancel (Nat.gcd_dvd_right b d)
  have har : (a : ℚ) = (a / a.gcd c : ℕ) * (a.gcd c : ℚ) := by
    exact (Nat.cast_mul _ _).symm.trans (congrArg (fun k : ℕ ↦ (k : ℚ)) han) |>.symm
  have hbr : (b : ℚ) = (b / b.gcd d : ℕ) * (b.gcd d : ℚ) := by
    exact (Nat.cast_mul _ _).symm.trans (congrArg (fun k : ℕ ↦ (k : ℚ)) hbn) |>.symm
  have hcr : (c : ℚ) = (c / a.gcd c : ℕ) * (a.gcd c : ℚ) := by
    exact (Nat.cast_mul _ _).symm.trans (congrArg (fun k : ℕ ↦ (k : ℚ)) hcn) |>.symm
  have hdr : (d : ℚ) = (d / b.gcd d : ℕ) * (b.gcd d : ℚ) := by
    exact (Nat.cast_mul _ _).symm.trans (congrArg (fun k : ℕ ↦ (k : ℚ)) hdn) |>.symm
  rw [har, hbr, hcr, hdr, Nat.cast_mul, Nat.cast_mul]
  have hgn : (a.gcd c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hg)
  have hhn : (b.gcd d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hh)
  have hbn0 : ((b / b.gcd d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb0)
  have hcn0 : ((c / a.gcd c : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc0)
  have hdn0 : ((d / b.gcd d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd0)
  field_simp [hgn, hhn, hbn0, hcn0, hdn0]

/-- For positive b and coprime natural a,b, the canonical rational a/b has
numerator absolute value a and denominator b. Apply the standard reduced-fraction formulas. -/
theorem num_den_of_coprime_nat {a b : ℕ} (hb : 0 < b) (hab : a.Coprime b) :
    (((a : ℚ) / b).num.natAbs = a) ∧ (((a : ℚ) / b).den = b) := by
  have hi : (a : ℤ).natAbs.Coprime (b : ℤ).natAbs := by simpa only [Int.natAbs_natCast] using hab
  have hn := Rat.num_div_eq_of_coprime (Int.natCast_pos.mpr hb) hi
  have hd := Rat.den_div_eq_of_coprime (Int.natCast_pos.mpr hb) hi
  simp only [Int.cast_natCast] at hn hd
  exact ⟨by rw [hn, Int.natAbs_natCast], Int.natCast_inj.mp hd⟩

/-- For two positive reduced natural fractions, the canonical numerator and denominator
of their quotient are the crossed gcd cofactors. Prove reduction is complete using coprimality. -/
theorem quotient_num_den_after_gcd {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a.Coprime b) (hcd : c.Coprime d) :
    ((((a : ℚ) / b) / ((c : ℚ) / d)).num.natAbs = (a / a.gcd c) * (d / b.gcd d)) ∧
      ((((a : ℚ) / b) / ((c : ℚ) / d)).den = (c / a.gcd c) * (b / b.gcd d)) := by
  rw [quotient_gcd_reduction ha hb hc hd]
  apply num_den_of_coprime_nat _ (coprime_cross_after_gcd ha hb hab hcd)
  apply mul_pos
  · exact Nat.div_pos (Nat.le_of_dvd hc (Nat.gcd_dvd_right a c)) (Nat.gcd_pos_of_pos_left c ha)
  · exact Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_left b d)) (Nat.gcd_pos_of_pos_left d hb)

/-- Every positive rational equals the quotient of its numerator absolute value
and positive denominator. Positivity removes the sign of the numerator. -/
theorem positive_rat_nat_fraction {q : ℚ} (hq : 0 < q) : q = (q.num.natAbs : ℚ) / q.den := by
  have hn : (q.num.natAbs : ℤ) = q.num := by
    rw [Int.natCast_natAbs, abs_of_pos (Rat.num_pos.mpr hq)]
  rw [← Int.cast_natCast, hn, Rat.num_div_den]

/-- For positive rationals q,r, compute the canonical quotient numerator and denominator
by canceling the numerator gcd and denominator gcd. This supplies the divisor encoding. -/
theorem positive_quotient_num_den {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    ((q / r).num.natAbs =
        (q.num.natAbs / q.num.natAbs.gcd r.num.natAbs) * (r.den / q.den.gcd r.den)) ∧
      ((q / r).den =
        (r.num.natAbs / q.num.natAbs.gcd r.num.natAbs) * (q.den / q.den.gcd r.den)) := by
  have hnq : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hq))
  have hnr : 0 < r.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hr))
  have he := quotient_num_den_after_gcd hnq q.den_pos hnr r.den_pos q.reduced r.reduced
  rw [← positive_rat_nat_fraction hq, ← positive_rat_nat_fraction hr] at he
  exact he

end PseudoPrime.NumberTheory.Heilbronn
