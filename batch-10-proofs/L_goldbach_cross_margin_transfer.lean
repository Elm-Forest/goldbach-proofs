import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_cross_margin_transfer :
    ∀ G K C T pp κ e : ℝ, |G-(K-C)| ≤ e → |C-T| ≤ κ → T ≤ K-2*κ → pp+e < κ → pp < G := by
  intro G K C T pp κ e h1 h2 h3 h4
  have ha := (abs_le.mp h1).1
  have hb := (abs_le.mp h2).2
  linarith
