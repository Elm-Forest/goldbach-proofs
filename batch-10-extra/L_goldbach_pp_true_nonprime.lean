import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pp_true_nonprime :
    ∀ p a : ℕ, p.Prime → 2≤a → ¬ Nat.Prime (p^a) := by
  intro p a hp ha h
  have hd : p ∣ p^a := dvd_pow_self _ (by omega)
  rcases (Nat.dvd_prime h).mp hd with h1 | h1
  · exact hp.ne_one h1
  · have h2 : p^2 ≤ p^a := Nat.pow_le_pow_right (by omega [hp.two_le]) ha
    nlinarith [hp.two_le]
