import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pp_divisor_coprime :
    ∀ p a n : ℕ, 0<a → ((p^a).Coprime n ↔ p.Coprime n) := by
  intro p a n ha
  first
  | exact Nat.Coprime.pow_left_iff ha
  | exact Nat.coprime_pow_left_iff ha
  | exact?
