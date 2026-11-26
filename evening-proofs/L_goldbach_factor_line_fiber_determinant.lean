import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_factor_line_fiber_determinant :
    ∀ (a b N r₀ s₀ g i j : ℤ), 0 < g → g ∣ a → g ∣ b → a*r₀+b*s₀=N → (r₀+(b/g)*i)*(s₀-(a/g)*j)-(r₀+(b/g)*j)*(s₀-(a/g)*i)=-(N/g)*(j-i) := by
  intro a b N r₀ s₀ g i j hg hda hdb hN
  have ha : a / g * g = a := Int.ediv_mul_cancel hda
  have hb : b / g * g = b := Int.ediv_mul_cancel hdb
  have hdN : g ∣ N := by
    rw [← hN]
    exact dvd_add (dvd_mul_of_dvd_left hda _) (dvd_mul_of_dvd_left hdb _)
  have hn : N / g * g = N := Int.ediv_mul_cancel hdN
  have hl : (a/g)*r₀+(b/g)*s₀ = N/g := by
    apply mul_right_cancel₀ (ne_of_gt hg)
    calc
      _ = (a/g*g)*r₀+(b/g*g)*s₀ := by ring
      _ = N := by rw [ha,hb,hN]
      _ = _ := hn.symm
  rw [← hl]
  ring
