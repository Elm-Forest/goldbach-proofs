import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_conductor_dyadic_scale :
    ∀ (c ε : ℝ), 0<c → 0<ε → ∀ k : ℕ, 4*c*Real.log 2/ε < (2:ℝ)^k → |4*c*Real.log 2/(2:ℝ)^k|<ε := by
  intro c ε hc he k hk
  have hp : 0 < (2:ℝ)^k := by positivity
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_of_nonneg (by positivity)]
  apply (div_lt_iff₀ hp).2
  have h := (div_lt_iff₀ he).1 hk
  linarith
