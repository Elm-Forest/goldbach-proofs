import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pp_cubic_base :
    ∀ p a n : ℕ, 1≤p → 3≤a → p^a≤n → p^3≤n := by
  intro p a n hp ha hn
  apply le_trans _ hn
  first
  | exact Nat.pow_le_pow_right hp ha
  | exact pow_le_pow_right₀ hp ha
  | exact?
