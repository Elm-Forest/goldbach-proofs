import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pp_base_cutoff :
    ∀ p a n : ℕ, 2≤p → 2≤a → p^a≤n → p≤Nat.sqrt n := by
  intro p a n hp ha hn
  have hh : p^2 ≤ p^a := by
    first
    | exact Nat.pow_le_pow_right (by omega) ha
    | exact pow_le_pow_right₀ (by omega) ha
    | exact?
  have h := hh.trans hn
  first
  | exact Nat.le_sqrt.mpr (by simpa [pow_two] using h)
  | exact Nat.le_sqrt.mpr h
  | exact?
