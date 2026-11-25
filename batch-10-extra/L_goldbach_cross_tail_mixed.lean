import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_cross_tail_mixed :
    ∀ (a b : ℂ), ‖a+b‖^2 - ‖a‖^2 - ‖b‖^2 = 2*(a*star b).re := by
  intro a b
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.add_re, Complex.add_im]
  ring
