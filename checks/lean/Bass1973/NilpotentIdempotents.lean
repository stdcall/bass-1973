import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring

/-!
# Uniqueness step for III §3, p.96

The printed equality `sqrt(eA) = eA` fails in a nonreduced ring. Its
correct form is `sqrt(eA) = eA + nil(A)`. The following checks cover the
algebraic uniqueness step: a nilpotent idempotent is zero; two commuting
idempotents whose complementary corners are nilpotent are equal.
The ideal-radical equality and the theorem producing an idempotent are
not formalized here.
-/

namespace Bass1973

theorem nilpotent_idempotent_zero {R : Type*} [MonoidWithZero R] (e : R)
    (he : e * e = e) (hn : IsNilpotent e) : e = 0 :=
  IsIdempotentElem.eq_zero_of_isNilpotent he hn

theorem idempotents_equal_of_nilpotent_corners {R : Type*} [CommRing R]
    (e f : R) (he : e * e = e) (hf : f * f = f)
    (hn₁ : IsNilpotent (e * (1 - f)))
    (hn₂ : IsNilpotent (f * (1 - e))) : e = f := by
  have corner (a b : R) (ha : a * a = a) (hb : b * b = b) :
      (a * (1 - b)) * (a * (1 - b)) = a * (1 - b) := by
    calc
      _ = (a * a) * (1 - 2 * b + b * b) := by ring
      _ = a * (1 - b) := by rw [ha, hb]; ring
  have h₁ := nilpotent_idempotent_zero _ (corner e f he hf) hn₁
  have h₂ := nilpotent_idempotent_zero _ (corner f e hf he) hn₂
  have h₁' : e = e * f := sub_eq_zero.mp (by simpa only [mul_sub, mul_one] using h₁)
  have h₂' : f = f * e := sub_eq_zero.mp (by simpa only [mul_sub, mul_one] using h₂)
  exact h₁'.trans ((mul_comm e f).trans h₂'.symm)

#print axioms nilpotent_idempotent_zero
#print axioms idempotents_equal_of_nilpotent_corners

end Bass1973
