import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pp_exp_cutoff :
    ∀ p a n : ℕ, 2≤p → p^a≤n → a≤Nat.log 2 n := by
  intro p a n hp hn
  have h : 2^a ≤ n := (Nat.pow_le_pow_left hp a).trans hn
  first
  | exact (Nat.le_log2 (by omega)).2 h
  | exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by positivity : 0 < n)).2 h
  | exact?
