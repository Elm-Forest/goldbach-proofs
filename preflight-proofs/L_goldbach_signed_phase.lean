import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_signed_phase :
    ∀ (u S M : ℂ) (E : ℝ), ‖u‖=1 → ‖S-M‖≤E → (u*M^2).re-E*(2*‖M‖+E)≤(u*S^2).re := by
  intro u S M E hu herr
  have hE : 0 ≤ E := (norm_nonneg _).trans herr
  have hsum : ‖S + M‖ ≤ 2 * ‖M‖ + E := by
    calc
      ‖S + M‖ = ‖(S - M) + (M + M)‖ := by
        rw [show S + M = (S - M) + (M + M) by ring]
      _ ≤ ‖S - M‖ + ‖M + M‖ := norm_add_le _ _
      _ ≤ 2 * ‖M‖ + E := by
        have hM := norm_add_le M M
        linarith
  have hsq : ‖S ^ 2 - M ^ 2‖ ≤ E * (2 * ‖M‖ + E) := by
    rw [show S ^ 2 - M ^ 2 = (S - M) * (S + M) by ring, norm_mul]
    exact mul_le_mul herr hsum (norm_nonneg _) hE
  have hn : ‖u * S ^ 2 - u * M ^ 2‖ ≤ E * (2 * ‖M‖ + E) := by
    rw [show u * S ^ 2 - u * M ^ 2 = u * (S ^ 2 - M ^ 2) by ring,
      norm_mul, hu, one_mul]
    exact hsq
  have hre : -‖u * S ^ 2 - u * M ^ 2‖ ≤ (u * S ^ 2 - u * M ^ 2).re := by
    have hh : |(u * S ^ 2 - u * M ^ 2).re| ≤ ‖u * S ^ 2 - u * M ^ 2‖ := by
      first
      | exact Complex.abs_re_le_norm _
      | exact?
    have hh' : -(u * S ^ 2 - u * M ^ 2).re ≤ ‖u * S ^ 2 - u * M ^ 2‖ := (neg_le_abs _).trans hh
    linarith
  rw [Complex.sub_re] at hre
  linarith
