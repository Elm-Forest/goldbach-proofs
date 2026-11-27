import Mathlib

/-!
Power-budget audit for the zero-density route to the wide inner remainder.
This file proves arithmetic scale inequalities only, not a zero-density
theorem, zero-free theorem, explicit formula, or the registered target.
Use base x = n, exponents a = log_n D, b = log_n X (dyadic endpoint),
c = log_n h, t = log_n T (zero-height block).
The proposed h is n D / u, capped at n/log^k n.
-/

namespace InnerFloorResearch.DensityBudget

/-- Uniform zero-density summation remains below the critical threshold:
(D² T)^3 / X² has a fixed power saving. -/
theorem densityExponent {a b c t : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/5)
    (hb : c ≤ b) (hb' : b ≤ 1)
    (ht : t ≤ 1/4)
    (hc : 5/6 - 1/1000 + a ≤ c ∨ 99/100 ≤ c) :
    3*(2*a+t)-2*b ≤ -(1/50) := by
  rcases hc with hc | hc <;> linarith

/-- The low-height block (T <= X/h) pays the zero-count Cauchy loss T
and the density factor (D² T)^(3/8). The resulting error ratio is
D^(3/4) X^(-1/4) T^(11/8). -/
theorem lowHeightExponent {a b c t : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/5)
    (hb : c ≤ b) (hb' : b ≤ 1)
    (ht : t ≤ b-c)
    (hc : 5/6 - 1/1000 + a ≤ c ∨ 99/100 ≤ c) :
    (3/4)*a-(1/4)*b+(11/8)*t ≤ -(1/100) := by
  rcases hc with hc | hc <;> linarith

/-- Above X/h, the explicit-formula window weight contributes
(X/(hT))², compensating for the extra height. -/
theorem highHeightExponent {a b c t : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/5)
    (hb : c ≤ b) (hb' : b ≤ 1)
    (ht : b-c ≤ t)
    (hc : 5/6 - 1/1000 + a ≤ c ∨ 99/100 ≤ c) :
    (3/4)*a-(1/4)*b+(11/8)*t+2*(b-c-t) ≤ -(1/100) := by
  rcases hc with hc | hc <;> linarith

/-- Summing the square of the classical truncation remainder X/T over
O(D²) primitive characters and dividing by h². Use T=n^(1/4). -/
theorem truncationExponent {a b c : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1/5)
    (hb' : b ≤ 1)
    (hc : 5/6 - 1/1000 + a ≤ c ∨ 99/100 ≤ c) :
    2*a+2*(b-1/4-c) ≤ -(1/20) := by
  rcases hc with hc | hc <;> linarith

/-- Generic conversion of certified exponent inequalities to real
power inequalities; no asymptotic assumption or floating-point arithmetic. -/
theorem realPowerBudget {n e δ : ℝ} (hn : 1 ≤ n) (he : e ≤ -δ) :
    n^e ≤ n^(-δ) := Real.rpow_le_rpow_of_exponent_le hn he

/-- The exact scale in the already accepted zero-sum mean-square theorem
is Q^2/(h/X) <= X^(5/12). This has uniform exponent slack. -/
theorem acceptedWindowScaleExponent {a b c : ℝ}
    (ha' : a ≤ 1/5) (hb' : b ≤ 1)
    (hc : 5/6 - 1/1000 + a ≤ c ∨ 99/100 ≤ c) :
    2*a+(7/12)*b-c ≤ -(1/200) := by
  rcases hc with hc | hc <;> linarith

end InnerFloorResearch.DensityBudget
