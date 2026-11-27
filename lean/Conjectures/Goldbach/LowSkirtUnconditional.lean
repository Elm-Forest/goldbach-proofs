import Mathlib
import Conjectures.Goldbach.ShortProgressionsMeanTheta
import Conjectures.Goldbach.LowSkirtFromShortProgressions

/-!
# Unconditional low-modulus Goldbach arc-skirt bound

Direct composition of two separately verified formalizations:
* `Conjectures.Goldbach.ShortProgressionsMeanTheta` (Koukoulopoulos,
  *Primes in short arithmetic progressions*, arXiv:1405.6592);
* `Conjectures.Goldbach.LowSkirtFromShortProgressions`, the verified
  analytic transfer from short-interval progression estimates to the
  frozen low-arc skirt integral.

No new axiom or unproved analytic assumption is introduced. This is a
separate auxiliary consequence, not a proof of the registered
`L-goldbach-wide-remainder-inner-floor` target.
-/

theorem Conjectures.Goldbach.LowSkirtUnconditional :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowSkirt := fun n : ℕ => intervalIntegral (fun t => (lowWideArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (lowSkirt n).re := by
  exact Conjectures.Goldbach.LowSkirtFromShortProgressions
    Conjectures.Goldbach.ShortProgressionsMeanTheta
