import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_unit_anti_range :
    ∀ n a b : ℕ, 0<a → a<n → 0<b → b<n → (n ∣ a+b ↔ a+b=n) := by
  intro n a b ha han hb hbn
  constructor
  · rintro ⟨k, hk⟩
    have h1 : 1 ≤ k := by
      by_contra! h
      have : k = 0 := by omega
      simp [this] at hk
      omega
    have h2 : k < 2 := by
      by_contra! h
      have hh := Nat.mul_le_mul_left n h
      omega
    have : k = 1 := by omega
    simpa [this] using hk
  · intro h
    rw [h]
