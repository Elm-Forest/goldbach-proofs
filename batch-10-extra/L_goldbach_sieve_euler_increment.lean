import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_sieve_euler_increment :
    ∀ p : ℕ, p.Prime → 2<p → (((1+1/((p:ℝ)-2))^2-1)/(p:ℝ)) ≤ 9/(p:ℝ)^2 := by
  intro p hp h
  have h3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast (show 3≤p by omega)
  have hp0 : (0:ℝ)<p := by linarith
  have hp2 : (0:ℝ)<(p:ℝ)-2 := by linarith
  apply (div_le_iff₀ hp0).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0<(p:ℝ)^2)).2
  field_simp
  nlinarith [sq_nonneg ((p:ℝ)-3)]
