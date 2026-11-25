import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_conductor_odd_fixed :
    ∀ (m : ℕ) (r : Fin m → Fin m) (v : Fin m → ℂ), (∀ i, v (r i)= -v i) → ∀ i, r i=i → v i=0 := by
  intro m r v hv i hi
  have h := hv i
  rw [hi] at h
  linear_combination h / 2
