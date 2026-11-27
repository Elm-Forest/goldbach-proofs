import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
# Wide Remainder Inner Floor — Unified Route B + Independent Odd-Residual Pre-PR File

Target task: `L-goldbach-wide-remainder-inner-floor`
Target file: `lean/Conjectures/Goldbach/WideRemainderInnerFloor.lean`

Unifies ALL independently Colab-verified Route B & independent-odd-residual modules
under pinned Lean 4.36.0 / Mathlib `fc4f59e`, standard foundational axioms only
(`propext`, `Classical.choice`, `Quot.sound`), zero `sorry`, zero GRH imports:
1. `InnerFloorOccurrence`: 3,218-line end-to-end tapered zero-occurrence residual floor.
2. `InnerFloorRouteB`: signed bilinear cell floor, model–bad cross vanishing at `q ∣ n`,
   primitive quadratic Gauss square, and 3-way parity/reality partition.
3. `InnerFloorRouteBThreshold`: even real diagonal nonnegativity and exact necessity /
   sufficiency log-gap thresholds.
4. `InnerFloorRouteBAlmostAll`: unconditional Gate-3 high-gcd exceptional-set density bound.
5. `InnerFloorRouteBFourGate`: 4-gate quantitative residual partition (adding imaginary height
   `|γ|` gate), exact joint Gauss–Ramanujan negative countermodel (`d = 3p`, `n = 2p^8`),
   and global mod-`3p` parity annihilation proof (`global_mod3_forced_one`, `global_modp_neg`).
6. `InnerFloorIndependentEulerMass` / `InnerFloorIndependentCross` /
   `InnerFloorIndependentRealKernel` / `InnerFloorIndependentRelativeSign`:
   odd squarefree totient tail, localized real-zero cross saving, finite-frequency
   real-kernel L2 perturbation `∫₀¹ (x^(β-1)-1)² dx ≤ (16/3)(1-β)²`, and weighted relative floor.
7. `Conjectures.Goldbach`: exact frozen statement with the single isolated open-problem
   barrier (`JointNegativeNearOneZeroBarrier`) explicitly declared at the top level.
-/



/-!
Small independently replayable arithmetic interface extracted from
ShortProgressionsMeanTheta (XBribo, PR #3789,
a546c6629fae0223b56067d5e4ebc34043c4fbf1, Apache-2.0).
Names relocated to avoid duplicate OAI.Ostmann declarations when used
with DyadicCellShortPrimeFloor. Only elementary definitions and lemmas
are copied; none of the analytic black-box conclusions are assumed.
-/
open Finset Filter
open scoped Topology Classical
noncomputable section
namespace InnerFloorLinearTotient
set_option maxHeartbeats 1000000 in


private def squareMass : ℝ := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
set_option maxHeartbeats 1000000 in

private theorem squareMass_nonneg : 0 ≤ squareMass := tsum_nonneg fun _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem sum_square_inv_le (s : Finset ℕ) :
    (∑ n ∈ s, ((n:ℝ)^2)⁻¹) ≤ squareMass :=
  (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2:ℕ))).sum_le_tsum s fun _ _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem one_le_squareMass : 1 ≤ squareMass := by
  simpa using sum_square_inv_le {(1:ℕ)}

set_option maxHeartbeats 1000000 in
/-- Uniform constant for the reciprocal-totient mean and conductor lifting. -/
def weightConstant : ℝ := Real.exp (2*squareMass) * squareMass
set_option maxHeartbeats 1000000 in

theorem weightConstant_nonneg : 0 ≤ weightConstant :=
  mul_nonneg (Real.exp_pos _).le squareMass_nonneg
set_option maxHeartbeats 1000000 in

private theorem prime_factor_bound {p : ℕ} (hp : 2 ≤ p) :
    (1-(p:ℝ)⁻¹)⁻¹ ≤ (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) := by
  let u := (p:ℝ)⁻¹
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu' : u ≤ 1/2 := by
    change (p:ℝ)⁻¹ ≤ 1/2
    rw [← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hp'
  have hden : 0 < 1-u := by linarith
  have hsq : u^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ hu hu' 2
  have hnon := mul_nonneg (sq_nonneg u) (show 0 ≤ 1-2*u^2 by linarith)
  rw [← inv_pow]
  change (1-u)⁻¹ ≤ (1+u)*(1+2*u^2)
  rw [← one_div, div_le_iff₀ hden]
  nlinarith only [hnon]
set_option maxHeartbeats 1000000 in

private theorem squarefree_product_eq (q : ℕ) (hq : 0 < q) :
    (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) = ∑ d ∈ q.divisors with Squarefree d, (d:ℝ)⁻¹ := by
  rw [Finset.prod_one_add, Nat.sum_divisors_filter_squarefree hq.ne', Nat.factors_eq]
  refine sum_congr rfl fun s _ => ?_
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod]
  rw [Finset.prod_eq_multiset_prod, show (fun i : ℕ => i) = id from rfl, Multiset.map_id]
set_option maxHeartbeats 1000000 in

private theorem ratio_le_divisors (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hEuler : (q.totient:ℝ) = (q:ℝ)*∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹) := by
    simpa only [map_natCast, map_mul, map_prod, map_sub, map_one, map_inv₀] using
      congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors q)
  have hlocal (p : ℕ) (hp : p ∈ q.primeFactors) : 0 ≤ (1-(p:ℝ)⁻¹)⁻¹ := by
    have hp' : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    apply inv_nonneg.mpr
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by linarith)
  have hsq : (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) ≤ Real.exp (2*squareMass) := by
    apply (Real.prod_one_add_le_exp_sum _ (fun _ => by positivity)).trans
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_square_inv_le _) (by norm_num)
  calc
    _ = ∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹)⁻¹ := by
      rw [hEuler, div_mul_eq_div_div, div_self hq'.ne', one_div, Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) :=
      prod_le_prod₀ hlocal fun p hp => prime_factor_bound (Nat.prime_of_mem_primeFactors hp).two_le
    _ = (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) :=
      Finset.prod_mul_distrib
    _ ≤ (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * Real.exp (2*squareMass) :=
      mul_le_mul_of_nonneg_left hsq (prod_nonneg fun _ _ => by positivity)
    _ ≤ _ := by
      rw [mul_comm, squarefree_product_eq q hq]
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)) (Real.exp_pos _).le
set_option maxHeartbeats 1000000 in

private theorem harmonic_bound (Q : ℕ) :
    (∑ i ∈ Icc 1 Q, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log Q

set_option maxHeartbeats 1000000 in
/-- Pointwise `q/φ(q)` also costs at most one logarithm. -/
theorem ratio_totient_le (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ weightConstant * (1+Real.log q) := by
  have hsub : q.divisors ⊆ Icc 1 q := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)⟩
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q from hq))
  calc
    _ ≤ Real.exp (2*squareMass) * (1+Real.log q) :=
      (ratio_le_divisors q hq).trans (mul_le_mul_of_nonneg_left
        ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (harmonic_bound q))
        (Real.exp_pos _).le)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (Real.exp_pos _).le one_le_squareMass) (by positivity)
set_option maxHeartbeats 1000000 in

private theorem sum_antidiagonal_le_product (Q : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal, f ab.1*g ab.2) ≤
      (∑ a ∈ Icc 1 Q, f a)*(∑ b ∈ Icc 1 Q, g b) := by
  let S := Icc 1 Q
  let w (p : ℕ × ℕ) := f p.1*g p.2
  have hw (p : ℕ × ℕ) : 0 ≤ w p := mul_nonneg (hf _) (hg _)
  have hsub (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal ⊆ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    intro ab hab
    have hm (d : ℕ) (hd : d ∈ q.divisors) : d ∈ S :=
      mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        (Nat.le_of_dvd (mem_Icc.mp hq).1 (Nat.dvd_of_mem_divisors hd)).trans (mem_Icc.mp hq).2⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
      hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
  change (∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab) ≤ _
  calc
    _ ≤ ∑ q ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w p :=
      sum_le_sum fun q hq => sum_le_sum_of_subset_of_nonneg (hsub q hq) (fun p _ _ => hw p)
    _ = ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w p :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ S ×ˢ S, w p := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hw p)
    _ = (∑ a ∈ S, f a)*(∑ b ∈ S, g b) := by rw [sum_product, sum_mul_sum]
set_option maxHeartbeats 1000000 in

private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1/(q.totient:ℝ) ≤ Real.exp (2*squareMass) *
      ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  calc
    _ = ((q:ℝ)/(q.totient:ℝ))/q := by
      rw [div_right_comm, div_self hq'.ne']
    _ ≤ (Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹)/q :=
      div_le_div_of_nonneg_right (ratio_le_divisors q hq) hq'.le
    _ = _ := by
      rw [mul_div_assoc, Finset.sum_div,
        ← Nat.sum_divisorsAntidiagonal (fun d _ => (d:ℝ)⁻¹/q) (n := q)]
      congr 1
      refine sum_congr rfl fun p hp => ?_
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul, div_eq_mul_inv,
        mul_inv, ← inv_pow, pow_two, mul_assoc]

set_option maxHeartbeats 1000000 in
/-- The sum of reciprocal totients costs one logarithm, uniformly in `Q`. -/
theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1/(q.totient:ℝ)) ≤ weightConstant * (1+Real.log Q) := by
  calc
    _ ≤ Real.exp (2*squareMass) * (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal,
        ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      exact sum_le_sum fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1
    _ ≤ Real.exp (2*squareMass) * ((∑ a ∈ Icc 1 Q, ((a:ℝ)^2)⁻¹)*(∑ b ∈ Icc 1 Q, (b:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (sum_antidiagonal_le_product Q (fun a => ((a:ℝ)^2)⁻¹) (fun b => (b:ℝ)⁻¹)
        (fun _ => by positivity) (fun _ => by positivity)) (Real.exp_pos _).le
    _ ≤ Real.exp (2*squareMass) * (squareMass*(1+Real.log Q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (sum_square_inv_le _) (harmonic_bound Q)
        (sum_nonneg fun _ _ => by positivity) squareMass_nonneg) (Real.exp_pos _).le
    _ = _ := (mul_assoc ..).symm

set_option maxHeartbeats 1000000 in
/-- Conductor multiplicities lose a single logarithm, including `d = 1`. -/
theorem sum_conductor_weights (Q : ℕ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ q ∈ Icc 1 Q, (∑ d ∈ q.divisors, F d)/(q.totient:ℝ)) ≤
      (∑ d ∈ Icc 1 Q, F d/(d.totient:ℝ)) * (weightConstant*(1+Real.log Q)) := by
  let f (d : ℕ) := F d/(d.totient:ℝ)
  let g (m : ℕ) := 1/(m.totient:ℝ)
  have hf (d : ℕ) : 0 ≤ f d := div_nonneg (hF d) (Nat.cast_nonneg _)
  have hg (m : ℕ) : 0 ≤ g m := by dsimp [g]; positivity
  have hterm (q : ℕ) : (∑ d ∈ q.divisors, F d)/(q.totient:ℝ) ≤
      ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := by
    rw [Finset.sum_div, ← Nat.sum_divisorsAntidiagonal (fun d _ => F d/(q.totient:ℝ)) (n := q)]
    refine sum_le_sum fun p hp => ?_
    have h1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    have h2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
    have h3 : 0 < (p.1.totient:ℝ)*(p.2.totient:ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.totient_pos.mpr h1) (Nat.totient_pos.mpr h2)
    have hφ := Nat.totient_super_multiplicative p.1 p.2
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1] at hφ
    calc
      _ ≤ F p.1/((p.1.totient:ℝ)*(p.2.totient:ℝ)) :=
        div_le_div_of_nonneg_left (hF _) h3 (by exact_mod_cast hφ)
      _ = _ := by
        simp only [f, g, div_eq_mul_inv, one_mul, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := sum_le_sum fun q _ => hterm q
    _ ≤ (∑ d ∈ Icc 1 Q, f d)*(∑ m ∈ Icc 1 Q, g m) := sum_antidiagonal_le_product Q f g hf hg
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_totient_le Q) (sum_nonneg fun d _ => hf d)


/-- Uniform finite sum of reciprocal m*phi(m), with no logarithmic loss.
The antidiagonal inequality uses the divisor expansion already proved above. -/
theorem sum_inv_mul_totient_le (M : ℕ) :
    (∑ m ∈ Icc 1 M, (1:ℝ)/((m:ℝ)*(m.totient:ℝ))) ≤
      weightConstant * squareMass := by
  calc
    _ ≤ Real.exp (2*squareMass) *
        (∑ m ∈ Icc 1 M, ∑ ab ∈ m.divisorsAntidiagonal,
          ((ab.1:ℝ)^2)⁻¹ * ((ab.2:ℝ)^2)⁻¹) := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro m hm
      have hm0 : 0 < (m:ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
      calc
        _ = (1/(m.totient:ℝ))/(m:ℝ) := by ring
        _ ≤ (Real.exp (2*squareMass) *
              ∑ ab ∈ m.divisorsAntidiagonal,
                ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹)/(m:ℝ) :=
          div_le_div_of_nonneg_right (inv_totient_le_pairs m (mem_Icc.mp hm).1) hm0.le
        _ = Real.exp (2*squareMass) *
              ∑ ab ∈ m.divisorsAntidiagonal,
                (((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹)/(m:ℝ) := by
          rw [mul_div_assoc, Finset.sum_div]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply sum_le_sum
          intro p hp
          have ha : 1 ≤ p.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
          have hb : 1 ≤ p.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
          have haR : (1:ℝ) ≤ p.1 := by exact_mod_cast ha
          have hbR : (1:ℝ) ≤ p.2 := by exact_mod_cast hb
          have ha0 : (0:ℝ) < p.1 := by linarith
          have hb0 : (0:ℝ) < p.2 := by linarith
          rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul]
          apply (div_le_iff₀ (mul_pos ha0 hb0)).2
          have h := mul_le_mul_of_nonneg_right haR (show 0 ≤ ((p.1:ℝ)^2)⁻¹ * (p.2:ℝ)⁻¹ by positivity)
          calc
            _ ≤ (p.1:ℝ) * (((p.1:ℝ)^2)⁻¹ * (p.2:ℝ)⁻¹) := by simpa using h
            _ = ((p.1:ℝ)^2)⁻¹ * ((p.2:ℝ)^2)⁻¹ * ((p.1:ℝ)*(p.2:ℝ)) := by
              field_simp <;> ring
    _ ≤ Real.exp (2*squareMass) *
        ((∑ a ∈ Icc 1 M, ((a:ℝ)^2)⁻¹) *
          (∑ b ∈ Icc 1 M, ((b:ℝ)^2)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (sum_antidiagonal_le_product M (fun a => ((a:ℝ)^2)⁻¹)
          (fun b => ((b:ℝ)^2)⁻¹) (fun _ => by positivity) (fun _ => by positivity))
        (Real.exp_pos _).le
    _ ≤ Real.exp (2*squareMass) * (squareMass * squareMass) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (sum_square_inv_le _) (sum_square_inv_le _)
          (sum_nonneg fun _ _ => by positivity) squareMass_nonneg) (Real.exp_pos _).le
    _ = _ := by unfold weightConstant; ring

/-- Explicit uniform constant, independent of the conductor and the cutoff. -/
def exceptionalWeightConstant : ℝ := weightConstant * squareMass

theorem exceptionalWeightConstant_nonneg : 0 ≤ exceptionalWeightConstant :=
  mul_nonneg weightConstant_nonneg squareMass_nonneg

/-- Finite weighted bound for the isolated zero-model diagonal.
The hypotheses expose the two analytic/arithmetic inputs separately:
the coefficient is bounded by 1/phi(m), and the integral by C*U/(d*m).
No assertion about actual prime sums is made. -/
theorem isolatedPacket_bound (S : Finset ℕ) (M d : ℕ) (hd : 0 < d)
    (hS : S ⊆ Icc 1 M) (U C X : ℝ) (hU : 0 ≤ U)
    (hC : 0 ≤ C) (hX : 0 ≤ X) (a I : ℕ → ℝ)
    (ha : ∀ m ∈ S, |a m| ≤ 1/(m.totient:ℝ))
    (hI : ∀ m ∈ S, |I m| ≤ C*U/((d:ℝ)*(m:ℝ))) :
    |((d:ℝ)/(d.totient:ℝ))*X*(∑ m ∈ S, a m * I m)| ≤
      C*exceptionalWeightConstant*X*U/(d.totient:ℝ) := by
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hphi : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hnon : 0 ≤ (d:ℝ)/(d.totient:ℝ)*X := by positivity
  have hsum : (∑ m ∈ S, 1/((m:ℝ)*(m.totient:ℝ))) ≤ exceptionalWeightConstant :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (sum_inv_mul_totient_le M)
  rw [abs_mul, abs_of_nonneg hnon]
  calc
    _ ≤ ((d:ℝ)/(d.totient:ℝ))*X*(∑ m ∈ S, |a m * I m|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hnon
    _ ≤ ((d:ℝ)/(d.totient:ℝ))*X*
        (∑ m ∈ S, (C*U/(d:ℝ))*(1/((m:ℝ)*(m.totient:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ hnon
      apply sum_le_sum
      intro m hm
      rw [abs_mul]
      calc
        _ ≤ (1/(m.totient:ℝ))*(C*U/((d:ℝ)*(m:ℝ))) :=
          mul_le_mul (ha m hm) (hI m hm) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ((d:ℝ)/(d.totient:ℝ))*X*(C*U/(d:ℝ)*exceptionalWeightConstant) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hnon
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp <;> ring

/-- The common-conductor packet estimate. For two primitive characters
of conductors d1 and d2, take L = lcm d1 d2 and g = sqrt(d1*d2).
The Gauss bound and the common-level totient inequality yield the
hypothesis on a. No sign or independence assumption is made. -/
theorem commonMultiplePacket_bound (S : Finset ℕ) (M L : ℕ) (hL : 0 < L)
    (hS : S ⊆ Icc 1 M) (g U C X : ℝ) (hg : 0 ≤ g) (hgL : g ≤ L)
    (hU : 0 ≤ U) (hC : 0 ≤ C) (hX : 0 ≤ X) (a I : ℕ → ℝ)
    (ha : ∀ m ∈ S, |a m| ≤ g/((L*m).totient:ℝ))
    (hI : ∀ m ∈ S, |I m| ≤ C*U/((L*m:ℕ):ℝ)) :
    |X*(∑ m ∈ S, a m * I m)| ≤
      C*exceptionalWeightConstant*X*U/(L.totient:ℝ) := by
  have hLR : 0 < (L:ℝ) := by exact_mod_cast hL
  have hphi : 0 < (L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hL
  have hsum : (∑ m ∈ S, 1/((m:ℝ)*(m.totient:ℝ))) ≤ exceptionalWeightConstant :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (sum_inv_mul_totient_le M)
  have hterm (m : ℕ) (hm : m ∈ S) :
      |a m*I m| ≤ (C*U/(L.totient:ℝ))*(1/((m:ℝ)*(m.totient:ℝ))) := by
    have hm0 : 0 < m := (mem_Icc.mp (hS hm)).1
    have hmR : 0 < (m:ℝ) := by exact_mod_cast hm0
    have hmφ : 0 < (m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm0
    have hφ : (L.totient:ℝ)*(m.totient:ℝ) ≤ ((L*m).totient:ℝ) := by
      exact_mod_cast Nat.totient_super_multiplicative L m
    have hal := (ha m hm).trans (div_le_div_of_nonneg_left hg (mul_pos hphi hmφ) hφ)
    rw [abs_mul]
    calc
      _ ≤ (g/((L.totient:ℝ)*(m.totient:ℝ)))*(C*U/((L*m:ℕ):ℝ)) :=
        mul_le_mul hal (hI m hm) (abs_nonneg _) (by positivity)
      _ ≤ ((L:ℝ)/((L.totient:ℝ)*(m.totient:ℝ)))*(C*U/((L*m:ℕ):ℝ)) := by
        gcongr
      _ = _ := by rw [Nat.cast_mul]; field_simp <;> ring
  rw [abs_mul,abs_of_nonneg hX]
  calc
    _ ≤ X*(∑ m ∈ S, |a m*I m|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hX
    _ ≤ X*(∑ m ∈ S, (C*U/(L.totient:ℝ))*(1/((m:ℝ)*(m.totient:ℝ)))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) hX
    _ ≤ X*(C*U/(L.totient:ℝ)*exceptionalWeightConstant) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum (by positivity)) hX
    _ = _ := by ring

/-- The conductor weight is uniformly little-o after any fixed polylog loss.
This handles arbitrary finite pairs whose lcm is at least n^(1/6+delta). -/
theorem eventualLargeConductorWeight (δ k ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      (n:ℝ)^(1/6+δ) ≤ d → d ≤ n →
      (Real.log (n:ℝ))^k*(n:ℝ)^(1/6:ℝ)/(d.totient:ℝ) ≤ ε := by
  have hnlim : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  let W := weightConstant
  have hW : 0 ≤ W := weightConstant_nonneg
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (k+1) hδ).comp_tendsto hnlim).bound
    (show 0 < ε/(2*W+1) by positivity)
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (Real.tendsto_log_atTop.comp hnlim).eventually_ge_atTop 1,hsmall]
    with n hn hlog hsmall
  intro d hd hdn
  let L := Real.log (n:ℝ)
  let v := (n:ℝ)^(1/6:ℝ)
  let w := (n:ℝ)^δ
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL1 : 1 ≤ L := hlog
  have hL0 : 0 < L := by linarith
  have hv : 0 < v := Real.rpow_pos_of_pos hn0 _
  have hw : 0 < w := Real.rpow_pos_of_pos hn0 _
  have hpow : v*w = (n:ℝ)^(1/6+δ) := by
    dsimp [v,w]
    rw [← Real.rpow_add hn0]
  have hvd : v*w ≤ (d:ℝ) := by rw [hpow]; exact hd
  have hdR : 0 < (d:ℝ) := (mul_pos hv hw).trans_le hvd
  have hdN : 0 < d := by exact_mod_cast hdR
  have hφ : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hdN
  have hdnR : (d:ℝ) ≤ n := by exact_mod_cast hdn
  have hlogd : Real.log (d:ℝ) ≤ L := Real.log_le_log hdR hdnR
  have hratio : (d:ℝ)/(d.totient:ℝ) ≤ 2*W*L := by
    calc
      _ ≤ W*(1+Real.log d) := ratio_totient_le d hdN
      _ ≤ W*(2*L) := mul_le_mul_of_nonneg_left (by linarith) hW
      _ = _ := by ring
  have hvw : v/(d:ℝ) ≤ 1/w := by
    rw [div_le_div_iff₀ hdR hw]
    simpa using hvd
  have hsl : L^(k+1) ≤ ε/(2*W+1)*w := by
    change ‖Real.log (n:ℝ)^(k+1)‖ ≤ ε/(2*W+1)*‖(n:ℝ)^δ‖ at hsmall
    simpa only [L,w,Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] using hsmall
  have hpowL : L^k*L = L^(k+1) := by
    rw [Real.rpow_add hL0,Real.rpow_one]
  change L^k*v/(d.totient:ℝ) ≤ ε
  calc
    _ = L^k*((d:ℝ)/(d.totient:ℝ))*(v/(d:ℝ)) := by field_simp <;> ring
    _ ≤ L^k*(2*W*L)*(1/w) := by gcongr
    _ = 2*W*(L^(k+1)/w) := by rw [← hpowL]; ring
    _ ≤ 2*W*(ε/(2*W+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_iff₀ hw).2 hsl
    _ ≤ ε := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 2*W+1)).2
      linarith

end InnerFloorLinearTotient

end



/-! Uniform, sign-independent estimates for the exact continuous zero
models on the scaled inner arcs. No zero-free hypothesis or assertion
about actual primes is used in these lemmas. -/
open MeasureTheory
open scoped Interval
namespace InnerFloorZeroModel
noncomputable section

def phase (s : ℝ) : ℂ := Complex.exp ((s:ℂ)*Complex.I)

@[simp] theorem norm_phase (s : ℝ) : ‖phase s‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I s

def transform (β γ v : ℝ) : ℂ :=
  ∫ x in (0:ℝ)..1, (x^(β-1):ℝ) • phase (γ*Real.log x + 2*Real.pi*v*x)

theorem transform_norm_le (β γ v : ℝ) (hβ : 0 < β) :
    ‖transform β γ v‖ ≤ 1/β := by
  unfold transform
  apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans_eq
  have he : (∫ x in (0:ℝ)..1,
        ‖(x^(β-1):ℝ) • phase (γ*Real.log x + 2*Real.pi*v*x)‖) =
      ∫ x in (0:ℝ)..1, x^(β-1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    change ‖(x^(β-1):ℝ) • phase (γ*Real.log x + 2*Real.pi*v*x)‖ = x^(β-1)
    rw [norm_smul, norm_phase, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx.1 _)]
  rw [he, integral_rpow (Or.inl (by linarith : -1 < β-1))]
  rw [show β-1+1=β by ring, Real.one_rpow, Real.zero_rpow hβ.ne', sub_zero]

def pairIntegral (β₁ γ₁ β₂ γ₂ L : ℝ) : ℂ :=
  ∫ v in (-L)..L, transform β₁ γ₁ v * transform β₂ γ₂ v *
    phase (-(2*Real.pi*v))

theorem pairIntegral_norm_le (β₁ γ₁ β₂ γ₂ L : ℝ)
    (h₁ : 0 < β₁) (h₂ : 0 < β₂) (hL : 0≤L) :
    ‖pairIntegral β₁ γ₁ β₂ γ₂ L‖ ≤ (2*L)/(β₁*β₂) := by
  unfold pairIntegral
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -L) (b := L) (C := (1/β₁)*(1/β₂))
    (f := fun v => transform β₁ γ₁ v * transform β₂ γ₂ v * phase (-(2*Real.pi*v)))
    (fun v _ => by
      rw [norm_mul, norm_mul, norm_phase, mul_one]
      exact mul_le_mul (transform_norm_le β₁ γ₁ v h₁)
        (transform_norm_le β₂ γ₂ v h₂) (norm_nonneg _) (by positivity))
  calc
    _ ≤ |L-(-L)| * ((1/β₁)*(1/β₂)) := by simpa [mul_comm] using h
    _ = _ := by rw [abs_of_nonneg (by linarith)]; ring

/-- Uniform bound for near-one pairs (valid throughout beta >= 1/2). -/
theorem pairIntegral_nearOne (β₁ γ₁ β₂ γ₂ L : ℝ)
    (h₁ : 1/2≤β₁) (h₂ : 1/2≤β₂) (hL : 0≤L) :
    ‖pairIntegral β₁ γ₁ β₂ γ₂ L‖ ≤ 8*L := by
  apply (pairIntegral_norm_le β₁ γ₁ β₂ γ₂ L (by linarith) (by linarith) hL).trans
  have hb : 1/4 ≤ β₁*β₂ := by
    have := mul_le_mul h₁ h₂ (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤β₁)
    linarith
  calc
    _ ≤ (2*L)/(1/4:ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hb
    _ = _ := by ring

end
end InnerFloorZeroModel

open Finset Filter InnerFloorLinearTotient
open scoped Classical Topology
namespace InnerFloorZeroModel
noncomputable section
set_option maxHeartbeats 2000000

/-- Actual continuous pair-integrals fit the verified conductor-packet
bound for all gamma, not just for real zeros. The arithmetic coefficient
bound must still be supplied by the actual Gauss-character expansion. -/
theorem continuousPacket_bound (S : Finset ℕ) (M L : ℕ) (hL : 0 < L)
    (hS : S ⊆ Icc 1 M) (g U X β₁ γ₁ β₂ γ₂ : ℝ)
    (hg : 0≤g) (hgL : g≤L) (hU : 0≤U) (hX : 0≤X)
    (hβ₁ : 1/2≤β₁) (hβ₂ : 1/2≤β₂)
    (a : ℕ → ℂ)
    (ha : ∀ m∈S, ‖a m‖≤g/((L*m).totient:ℝ)) :
    ‖(X:ℂ)*(∑ m∈S, a m * pairIntegral β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ)))‖ ≤
      8*exceptionalWeightConstant*X*U/(L.totient:ℝ) := by
  let I (m : ℕ) := pairIntegral β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ))
  have hI : ∀ m∈S, |‖I m‖|≤8*U/((L*m:ℕ):ℝ) := by
    intro m hm
    rw [abs_of_nonneg (norm_nonneg _)]
    have h := pairIntegral_nearOne β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ))
      hβ₁ hβ₂ (by positivity)
    dsimp [I]
    exact h.trans_eq (by ring)
  have hW := commonMultiplePacket_bound S M L hL hS g U 8 X hg hgL hU
    (by norm_num) hX (fun m => ‖a m‖) (fun m => ‖I m‖)
    (fun m hm => by simpa only [abs_of_nonneg (norm_nonneg _)] using ha m hm) hI
  have hsum0 : 0≤X*(∑ m∈S, ‖a m‖*‖I m‖) :=
    mul_nonneg hX (sum_nonneg fun m _ => by positivity)
  rw [abs_of_nonneg hsum0] at hW
  change ‖(X:ℂ)*(∑ m∈S, a m*I m)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX]
  apply le_trans _ hW
  apply mul_le_mul_of_nonneg_left _ hX
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])

/-- A finite family of large-common-conductor model pairs with any fixed
polylogarithmic cardinality and beta <= 1 is negligible in total.
The input U <= C * log(n)^2 * n^(1/6) is the frozen inner width. -/
theorem sparseLargePackets_o (δ k C ε : ℝ) (hδ : 0 < δ) (hC : 0≤C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (T : Finset ℕ) (D : ℕ → ℕ) (J : ℕ → ℂ),
        (T.card:ℝ) ≤ (Real.log (n:ℝ))^k →
        (∀ i∈T, (n:ℝ)^(1/6+δ)≤D i ∧ D i≤n) →
        (∀ i∈T, ‖J i‖ ≤ C*(n:ℝ)*(Real.log (n:ℝ))^2*
          (n:ℝ)^(1/6:ℝ)/( (D i).totient:ℝ)) →
        ‖∑ i∈T, J i‖ ≤ ε*(n:ℝ) := by
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (Real.tendsto_log_atTop.comp hlim).eventually_ge_atTop 1,
    eventualLargeConductorWeight δ (k+2) (ε/(C+1)) hδ (by positivity)]
    with n hn hlog hweight
  intro T D J hcard hD hJ
  let L := Real.log (n:ℝ)
  let v := (n:ℝ)^(1/6:ℝ)
  have hL1 : 1≤L := hlog
  have hL : 0 < L := by linarith
  have hpow : 0 < L^k := Real.rpow_pos_of_pos hL _
  have hLadd : L^(k+2) = L^k*L^2 := by rw [Real.rpow_add hL, Real.rpow_two]
  have hterm (i : ℕ) (hi : i∈T) :
      ‖J i‖ ≤ ε*(n:ℝ)/L^k := by
    obtain ⟨h₁,h₂⟩ := hD i hi
    have hw := hweight (D i) h₁ h₂
    change L^(k+2)*v/((D i).totient:ℝ) ≤ ε/(C+1) at hw
    rw [hLadd] at hw
    apply (le_div_iff₀ hpow).2
    calc
      ‖J i‖*L^k ≤ (C*(n:ℝ)*L^2*v/((D i).totient:ℝ))*L^k :=
        mul_le_mul_of_nonneg_right (hJ i hi) hpow.le
      _ = C*(n:ℝ)*(L^k*L^2*v/((D i).totient:ℝ)) := by ring
      _ ≤ C*(n:ℝ)*(ε/(C+1)) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ ε*(n:ℝ) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < C+1)).2
        nlinarith only [mul_nonneg hε.le (Nat.cast_nonneg n : (0:ℝ)≤n)]
  calc
    _ ≤ ∑ i∈T, ‖J i‖ := norm_sum_le _ _
    _ ≤ ∑ i∈T, ε*(n:ℝ)/L^k := sum_le_sum hterm
    _ = (T.card:ℝ)*(ε*(n:ℝ)/L^k) := by simp
    _ ≤ L^k*(ε*(n:ℝ)/L^k) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

end
end InnerFloorZeroModel
#print axioms InnerFloorZeroModel.continuousPacket_bound
#print axioms InnerFloorZeroModel.sparseLargePackets_o

/-!
The Gauss lifting lemmas below are extracted from the community's accepted
PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4, as stored in
alternate-signed/Type2B1B4Accepted.lean from the official main checkout.
Original proofs are retained; only the small necessary namespaces are used.
Apache-2.0 upstream license. This is a research-only standalone replay.
-/
open Finset
namespace BombieriVinogradov.LargeSieve
open Complex Real
noncomputable section
def additivePhase (x : ℝ) : ℂ := circleMap 0 1 (2 * Real.pi * x)

theorem additivePhase_add (x y : ℝ) : additivePhase (x + y) = additivePhase x * additivePhase y := by
  dsimp [additivePhase]
  rw [circleMap_zero_mul, one_mul, mul_add]


end
end BombieriVinogradov.LargeSieve
namespace DyadicMixedB4DualCharacter
theorem sum_natCast_range_eq_zmod {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q] (f : ZMod q → R) :
    ∑ u ∈ range q, f (u : ZMod q) = ∑ z : ZMod q, f z := by
  apply sum_bij (s := range q) (t := (univ : Finset (ZMod q))) (fun u _ => (u : ZMod q))
  · simp
  · intro u uMember v vMember equal
    have valEqual := congrArg ZMod.val equal
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp uMember),
      Nat.mod_eq_of_lt (mem_range.mp vMember)] using valEqual
  · intro z _
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · intro u _
    rfl


end DyadicMixedB4DualCharacter

section

open Finset BombieriVinogradov.LargeSieve DyadicMixedB4DualCharacter
open scoped Classical

namespace DyadicMixedB4GaussLift

noncomputable section

theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (d f : ℕ) (F : ℕ → R) :
    ∑ x ∈ range (d * f), F x = ∑ j ∈ range f, ∑ a ∈ range d, F (d * j + a) := by
  induction f with
  | zero => simp
  | succ f ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

theorem stdAddChar_nat_fraction {q : ℕ} [NeZero q] (k : ℕ) :
    ZMod.stdAddChar (k : ZMod q) = additivePhase ((k : ℝ) / q) := by
  rw [← Int.cast_natCast k, ZMod.stdAddChar_coe]
  unfold additivePhase
  rw [circleMap_zero, Complex.ofReal_one, one_mul]
  push_cast
  congr 1
  ring

theorem stdAddChar_mul_nat_fraction {q : ℕ} [NeZero q] (k a : ℕ) :
    ZMod.stdAddChar ((k : ZMod q) * (a : ZMod q)) = additivePhase ((k : ℝ) * a / q) := by
  rw [← Nat.cast_mul, stdAddChar_nat_fraction, Nat.cast_mul]

set_option maxHeartbeats 600000 in
theorem sum_phase_fraction_eq_if_dvd {q : ℕ} [NeZero q] (k : ℕ) :
    (∑ a ∈ range q, additivePhase ((k : ℝ) * a / q)) = if q ∣ k then (q : ℂ) else 0 := by
  simp_rw [← stdAddChar_mul_nat_fraction]
  rw [sum_natCast_range_eq_zmod (fun z => ZMod.stdAddChar ((k : ZMod q) * z))]
  simp_rw [mul_comm (k : ZMod q)]
  rw [AddChar.sum_mulShift (k : ZMod q) (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  have zeroIff : (k : ZMod q) = 0 ↔ q ∣ k := by rw [ZMod.natCast_eq_zero_iff]
  by_cases divides : q ∣ k
  · simp [divides, zeroIff.mpr divides]
  · have nonzero : (k : ZMod q) ≠ 0 := fun zero => divides (zeroIff.mp zero)
    simp [divides, nonzero]

theorem gaussSum_as_fraction_sum {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod d)) =
      ∑ a ∈ range d, χ (a : ZMod d) * additivePhase ((k : ℝ) * a / d) := by
  unfold gaussSum
  rw [← sum_natCast_range_eq_zmod]
  simp_rw [AddChar.mulShift_apply, stdAddChar_mul_nat_fraction]

set_option maxHeartbeats 600000 in
theorem lift_gaussSum {d f : ℕ} [NeZero d] [NeZero f]
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    (∑ u ∈ range (d * f), χ (u : ZMod d) * additivePhase ((k : ℝ) * u / ((d : ℝ) * f))) =
      if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
  have dNonzero : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have fNonzero : (f : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne f
  rw [sum_range_blocks, Finset.sum_comm]
  have liftEntry (a j : ℕ) :
      χ ((d * j + a : ℕ) : ZMod d) * additivePhase ((k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f)) =
        (χ (a : ZMod d) * additivePhase ((k : ℝ) * a / ((d : ℝ) * f))) *
          additivePhase ((k : ℝ) * j / f) := by
    have angle : (k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f) =
        (k : ℝ) * a / ((d : ℝ) * f) + (k : ℝ) * j / f := by
      push_cast
      field_simp
      ring
    rw [angle, additivePhase_add, ← mul_assoc]
    have same : ((d * j + a : ℕ) : ZMod d) = (a : ZMod d) := by push_cast; simp
    rw [same]
  simp_rw [liftEntry, ← mul_sum, sum_phase_fraction_eq_if_dvd]
  by_cases divisible : f ∣ k
  · simp only [if_pos divisible, ← Finset.sum_mul, gaussSum_as_fraction_sum]
    rw [mul_comm _ (f : ℂ)]
    apply congrArg (fun z : ℂ => (f : ℂ) * z)
    refine sum_congr rfl fun a _ => ?_
    have h : (k : ℝ) = ((k / f : ℕ) : ℝ) * f := by
      exact_mod_cast (Nat.div_mul_cancel divisible).symm
    have sameAngle : (k : ℝ) * a / ((d : ℝ) * f) = (((k / f : ℕ) : ℝ)) * a / d := by
      conv_lhs => rw [h]
      field_simp
    rw [sameAngle]
  · simp [divisible]


end
end DyadicMixedB4GaussLift

end

section

open Finset ArithmeticFunction BombieriVinogradov.LargeSieve DyadicMixedB4GaussLift
open scoped ArithmeticFunction.Moebius Classical

namespace DyadicMixedB4MoebiusGauss

noncomputable section

def moebiusComplex (m : ℕ) : ℂ := (μ m : ℂ)

theorem norm_moebiusComplex_le_one (m : ℕ) : ‖moebiusComplex m‖ ≤ 1 := by
  rw [moebiusComplex, Complex.norm_intCast]
  exact_mod_cast (abs_moebius_le_one (n := m))

theorem moebius_coprime_indicator {M : ℕ} (MPositive : 0 < M) (u : ℕ) :
    (∑ e ∈ M.divisors.filter (fun e => e ∣ u), moebiusComplex e) =
      if u.Coprime M then (1 : ℂ) else 0 := by
  let g := u.gcd M
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_right u MPositive
  have divisorsEquality : M.divisors.filter (fun e => e ∣ u) = g.divisors := by
    ext e
    rw [mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨eDividesM, _⟩, eDividesU⟩
      exact ⟨Nat.dvd_gcd eDividesU eDividesM, gPositive.ne'⟩
    · rintro ⟨eDividesG, _⟩
      exact ⟨⟨eDividesG.trans (Nat.gcd_dvd_right u M), MPositive.ne'⟩,
        eDividesG.trans (Nat.gcd_dvd_left u M)⟩
  have convolution : (∑ e ∈ g.divisors, μ e) = (1 : ArithmeticFunction ℤ) g := by
    rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta]
  rw [divisorsEquality]
  simp_rw [moebiusComplex, ← Int.cast_sum, convolution]
  change (((1 : ArithmeticFunction ℤ) g : ℤ) : ℂ) = if g = 1 then (1 : ℂ) else 0
  by_cases one : g = 1
  · simp [one, one_apply]
  · simp [one, one_apply]

theorem changeLevel_nat_indicator {d M : ℕ} (dDivides : d ∣ M) (χ : DirichletCharacter ℂ d)
    (u : ℕ) : DirichletCharacter.changeLevel dDivides χ (u : ZMod M) =
      (if u.Coprime M then (1 : ℂ) else 0) * χ (u : ZMod d) := by
  by_cases coprime : u.Coprime M
  · rw [if_pos coprime, one_mul]
    have same := DirichletCharacter.changeLevel_eq_cast_of_dvd χ dDivides (ZMod.unitOfCoprime u coprime)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast dDivides] at same
    exact same
  · rw [if_neg coprime, zero_mul]
    exact MulChar.map_nonunit _ (fun unit => coprime ((ZMod.isUnit_iff_coprime u M).mp unit))

theorem sum_filter_dvd_range {R : Type*} [AddCommMonoid R] {e M : ℕ}
    (ePositive : 0 < e) (eDivides : e ∣ M) (F : ℕ → R) :
    (∑ u ∈ (range M).filter (fun u => e ∣ u), F u) = ∑ v ∈ range (M / e), F (e * v) := by
  have quotient : e * (M / e) = M := Nat.mul_div_cancel' eDivides
  symm
  apply sum_bij (s := range (M / e)) (t := (range M).filter (fun u => e ∣ u)) (fun v _ => e * v)
  · intro v vMember
    refine mem_filter.mpr ⟨mem_range.mpr ?_, dvd_mul_right e v⟩
    rw [← quotient]
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp vMember) ePositive
  · intro v _ w _ eq
    exact Nat.eq_of_mul_eq_mul_left ePositive eq
  · intro u uMember
    obtain ⟨uRange, v, h⟩ := mem_filter.mp uMember
    refine ⟨v, mem_range.mpr ?_, h.symm⟩
    have prodLt : e * v < e * (M / e) := h ▸ quotient.symm ▸ mem_range.mp uRange
    exact Nat.lt_of_mul_lt_mul_left prodLt
  · intro v _
    rfl

theorem sum_inducedGauss_moebius {d M : ℕ} [NeZero M] (dDivides : d ∣ M)
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M)) =
      ∑ e ∈ M.divisors, moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) * additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) := by
  rw [gaussSum_as_fraction_sum]
  calc
    _ = ∑ u ∈ range M, ∑ e ∈ M.divisors.filter (fun e => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      refine sum_congr rfl fun u _ => ?_
      rw [changeLevel_nat_indicator, ← moebius_coprime_indicator (NeZero.pos M), mul_assoc, sum_mul]
    _ = ∑ e ∈ M.divisors, ∑ u ∈ (range M).filter (fun u => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = _ := by
      refine sum_congr rfl fun e eMember => ?_
      have eDivides := (Nat.mem_divisors.mp eMember).1
      have ePositive := Nat.pos_of_mem_divisors eMember
      have eNonzero : (e : ℝ) ≠ 0 := by exact_mod_cast ePositive.ne'
      have MNonzero : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
      have quotientNonzero : ((M / e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast quotientPositive.ne'
      have quotient : (M : ℝ) = e * ((M / e : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' eDivides).symm
      rw [sum_filter_dvd_range ePositive eDivides, mul_sum]
      refine sum_congr rfl fun v _ => ?_
      have scales : (k : ℝ) * (e * v : ℕ) / M = (k : ℝ) * v / ((M / e : ℕ) : ℝ) := by
        push_cast
        rw [quotient]
        field_simp
      rw [scales, Nat.cast_mul, map_mul]
      ring


end
end DyadicMixedB4MoebiusGauss

end

section

open Finset DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss
open scoped Classical

namespace DyadicMixedB4ImprimitiveBound

noncomputable section

theorem norm_primitive_gauss_shift_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (primitive : χ.IsPrimitive) (x : ZMod d) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ ≤ Real.sqrt d := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar primitive, norm_mul,
    DirichletCharacter.norm_gaussSum_stdAddChar primitive]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (DirichletCharacter.norm_le_one _ _)

theorem conductor_cofactor {M d e : ℕ} [NeZero d] [NeZero M] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (coprime : e.Coprime d) :
    0 < M / e / d ∧ d * (M / e / d) = M / e ∧ e * (d * (M / e / d)) = M := by
  have eDivides := (Nat.mem_divisors.mp eMember).1
  have ePositive := Nat.pos_of_mem_divisors eMember
  have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
  have joint : e * d ∣ M := coprime.mul_dvd_of_dvd_of_dvd eDivides dDivides
  have dividesQuotient : d ∣ M / e := (Nat.dvd_div_iff_mul_dvd eDivides).mpr (by simpa [mul_comm] using joint)
  have quotient := Nat.mul_div_cancel' dividesQuotient
  exact ⟨Nat.div_pos (Nat.le_of_dvd quotientPositive dividesQuotient) (NeZero.pos d), quotient,
    by rw [quotient, Nat.mul_div_cancel' eDivides]⟩

theorem norm_induced_gauss_term {M d e : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (k : ℕ) {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) :
    ‖moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) *
          BombieriVinogradov.LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ)))‖ ≤
      if e.Coprime d ∧ (M / e / d) ∣ k then ((M / e / d : ℕ) : ℝ) * Real.sqrt d else 0 := by
  by_cases coprime : e.Coprime d
  · obtain ⟨fPositive, hFactor, _⟩ := conductor_cofactor dDivides eMember coprime
    let f := M / e / d
    letI : NeZero f := ⟨fPositive.ne'⟩
    have liftIdentity : (∑ v ∈ range (M / e), χ (v : ZMod d) *
        BombieriVinogradov.LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) =
        if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
      convert lift_gaussSum (f := f) χ k using 1
      rw [show (M / e : ℕ) = d * f from hFactor.symm, Nat.cast_mul]
    rw [liftIdentity]
    by_cases divides : f ∣ k
    · have divides' : (M / e / d) ∣ k := divides
      have relevant : e.Coprime d ∧ (M / e / d) ∣ k := ⟨coprime, divides'⟩
      simp only [if_pos divides, if_pos relevant, norm_mul, Complex.norm_natCast]
      have factor : ‖moebiusComplex e‖ * ‖χ (e : ZMod d)‖ ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)).trans
          (by simpa only [mul_one] using norm_moebiusComplex_le_one e)
      refine (mul_le_of_le_one_left (by positivity) factor).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_primitive_gauss_shift_le primitive _) (Nat.cast_nonneg _)
    · have divides' : ¬(M / e / d) ∣ k := divides
      simp [divides, divides', coprime]
  · have valZero : χ (e : ZMod d) = 0 := MulChar.map_nonunit _
      (fun h => coprime ((ZMod.isUnit_iff_coprime e d).mp h))
    simp [coprime, valZero]

theorem norm_induced_gauss_le {M d : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M))‖ ≤
      Real.sqrt d * ∑ f ∈ k.divisors.filter (fun f => d * f ∣ M), (f : ℝ) := by
  let cof (e : ℕ) := M / e / d
  let support := M.divisors.filter (fun e => e.Coprime d ∧ cof e ∣ k)
  let bound := k.divisors.filter (fun f => d * f ∣ M)
  have imageSubset : support.image cof ⊆ bound := by
    intro f member
    obtain ⟨e, eMember, rfl⟩ := mem_image.mp member
    obtain ⟨divisor, coprime, divides⟩ := mem_filter.mp eMember
    obtain ⟨_, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides, kPositive.ne'⟩,
      ⟨e, by rw [mul_comm]; exact identity.symm⟩⟩
  have injectiveOn : Set.InjOn cof (support : Set ℕ) := by
    intro e eMember e' e'Member same
    obtain ⟨divisor, coprime, _⟩ := mem_filter.mp eMember
    obtain ⟨divisor', coprime', _⟩ := mem_filter.mp e'Member
    obtain ⟨fPositive, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    obtain ⟨_, _, identity'⟩ := conductor_cofactor dDivides divisor' coprime'
    change e * (d * cof e) = M at identity
    change e' * (d * cof e') = M at identity'
    rw [← same] at identity'
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (NeZero.pos d) fPositive) (identity.trans identity'.symm)
  have sumBound : (∑ e ∈ support, (cof e : ℝ)) ≤ ∑ f ∈ bound, (f : ℝ) := by
    rw [← sum_image injectiveOn]
    exact sum_le_sum_of_subset_of_nonneg imageSubset fun _ _ _ => Nat.cast_nonneg _
  rw [sum_inducedGauss_moebius]
  refine (norm_sum_le _ _).trans ?_
  have boundTerms := sum_le_sum (s := M.divisors)
    (fun e member => norm_induced_gauss_term dDivides member k primitive)
  refine boundTerms.trans ?_
  change (∑ e ∈ M.divisors, if e.Coprime d ∧ cof e ∣ k then (cof e : ℝ) * Real.sqrt d else 0) ≤
    Real.sqrt d * ∑ f ∈ bound, (f : ℝ)
  rw [← sum_filter, ← sum_mul, mul_comm (Real.sqrt d)]
  exact mul_le_mul_of_nonneg_right sumBound (Real.sqrt_nonneg _)


end
end DyadicMixedB4ImprimitiveBound

end

open Finset DyadicMixedB4ImprimitiveBound
namespace DyadicMixedB4CharacterFactorBound
noncomputable section
theorem norm_dirichlet_gauss_induced {r q : ℕ} [NeZero r] [NeZero q] (rDivides : r ∣ q)
    (χ : DirichletCharacter ℂ r) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel rDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod q))‖ ≤
      Real.sqrt χ.conductor * ∑ f ∈ k.divisors.filter (fun f => χ.conductor * f ∣ q), (f : ℝ) := by
  have conductorNonzero : χ.conductor ≠ 0 := fun zero => NeZero.ne r
    (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp zero)
  letI : NeZero χ.conductor := ⟨conductorNonzero⟩
  have inductionBound := norm_induced_gauss_le (χ.conductor_dvd_level.trans rDivides)
    χ.primitiveCharacter_isPrimitive k kPositive
  rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level rDivides,
    DirichletCharacter.changeLevel_primitiveCharacter] at inductionBound
  exact inductionBound

theorem norm_dirichlet_gauss_standard {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt χ.conductor := by
  have induced := norm_dirichlet_gauss_induced (dvd_refl r) χ 1 (by decide)
  have onlyOne : ((1 : ℕ).divisors.filter (fun f => χ.conductor * f ∣ r)) = {1} := by
    ext f
    simp only [Nat.divisors_one, mem_filter, mem_singleton]
    constructor
    · exact And.left
    · rintro rfl
      exact ⟨rfl, by simpa only [mul_one] using χ.conductor_dvd_level⟩
  rw [onlyOne] at induced
  simpa [DirichletCharacter.changeLevel_self, AddChar.mulShift_one] using induced

end
end DyadicMixedB4CharacterFactorBound

namespace InnerFloorGaussPacket
open Finset AddChar Complex
open scoped Classical ComplexConjugate
open DyadicMixedB4CharacterFactorBound
noncomputable section
set_option maxHeartbeats 2000000
variable {q : ℕ} [NeZero q]

/-- The exact additiveWeight used in the accepted canonical zero correction. -/
def canonicalWeight (a : ZMod q) (χ : DirichletCharacter ℂ q) : ℂ :=
  conj (∑ r : ZMod q, conj (ZMod.stdAddChar (a*r))*χ r) / (q.totient:ℂ)

theorem canonicalWeight_eq (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    canonicalWeight (a:ZMod q) χ =
      χ (a:ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar / (q.totient:ℂ) := by
  unfold canonicalWeight
  have he : conj (∑ r : ZMod q, conj (ZMod.stdAddChar ((a:ZMod q)*r))*χ r) =
      gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (a:ZMod q)) := by
    rw [map_sum,gaussSum]
    apply sum_congr rfl
    intro r _
    rw [map_mul]
    change star (star (ZMod.stdAddChar ((a:ZMod q)*r))) * star (χ r) = _
    rw [star_star,MulChar.star_apply',AddChar.mulShift_apply,mul_comm]
  rw [he,gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar a,inv_inv]

theorem canonicalWeight_norm (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    ‖canonicalWeight (a:ZMod q) χ‖ ≤ Real.sqrt χ.conductor/(q.totient:ℝ) := by
  rw [canonicalWeight_eq,norm_div,norm_mul,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at h
  exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans h

/-- Signed coefficient at an arbitrary real shift. A phase need only have
norm at most one; no independence or favourable sign is assumed. -/
def canonicalPairCoefficient (χ ψ : DirichletCharacter ℂ q)
    (phase : (ZMod q)ˣ → ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ, canonicalWeight (a:ZMod q) χ *
    canonicalWeight (a:ZMod q) ψ * phase a

theorem canonicalPairCoefficient_bound (χ ψ : DirichletCharacter ℂ q)
    (phase : (ZMod q)ˣ → ℂ) (hp : ∀ a, ‖phase a‖ ≤ 1) :
    ‖canonicalPairCoefficient χ ψ phase‖ ≤
      Real.sqrt χ.conductor * Real.sqrt ψ.conductor / (q.totient:ℝ) := by
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  unfold canonicalPairCoefficient
  calc
    _ ≤ ∑ a : (ZMod q)ˣ, ‖canonicalWeight (a:ZMod q) χ *
        canonicalWeight (a:ZMod q) ψ * phase a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod q)ˣ,
        (Real.sqrt χ.conductor/(q.totient:ℝ))*
        (Real.sqrt ψ.conductor/(q.totient:ℝ)) := by
      apply sum_le_sum
      intro a _
      rw [norm_mul,norm_mul]
      calc
        _ ≤ ‖canonicalWeight (a:ZMod q) χ‖ * ‖canonicalWeight (a:ZMod q) ψ‖ :=
          mul_le_of_le_one_right (by positivity) (hp a)
        _ ≤ _ := mul_le_mul (canonicalWeight_norm a χ) (canonicalWeight_norm a ψ)
          (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [sum_const,Finset.card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul]
      field_simp

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.canonicalWeight_eq
#print axioms InnerFloorGaussPacket.canonicalWeight_norm
#print axioms InnerFloorGaussPacket.canonicalPairCoefficient_bound

namespace InnerFloorGaussPacket
open Finset AddChar Complex InnerFloorLinearTotient InnerFloorZeroModel
open scoped Classical ComplexConjugate
noncomputable section
set_option maxHeartbeats 2000000

variable {q : ℕ} [NeZero q]

theorem signedPair_eq (χ ψ : DirichletCharacter ℂ q) (n : ZMod q) :
    canonicalPairCoefficient χ ψ
      (fun a => ZMod.stdAddChar (-n*(a:ZMod q))) =
      (gaussSum χ⁻¹ ZMod.stdAddChar * gaussSum ψ⁻¹ ZMod.stdAddChar /
        (q.totient:ℂ)^2) *
        gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-n)) := by
  have hφ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  unfold canonicalPairCoefficient
  simp_rw [canonicalWeight_eq]
  have ht (a : (ZMod q)ˣ) :
      (χ (a:ZMod q)*gaussSum χ⁻¹ ZMod.stdAddChar/(q.totient:ℂ)) *
        (ψ (a:ZMod q)*gaussSum ψ⁻¹ ZMod.stdAddChar/(q.totient:ℂ)) *
          ZMod.stdAddChar (-n*(a:ZMod q)) =
      (gaussSum χ⁻¹ ZMod.stdAddChar * gaussSum ψ⁻¹ ZMod.stdAddChar /
        (q.totient:ℂ)^2) *
        ((χ*ψ) (a:ZMod q)*ZMod.stdAddChar (-n*(a:ZMod q))) := by
    rw [MulChar.mul_apply]
    field_simp
    <;> ring
  simp_rw [ht,← Finset.mul_sum]
  congr 1
  let F : ZMod q → ℂ := fun a => (χ*ψ) a * ZMod.stdAddChar (-n*a)
  change (∑ a : (ZMod q)ˣ, F (a:ZMod q)) = ∑ a : ZMod q, F a
  let S := (Finset.univ : Finset (ZMod q)).filter IsUnit
  have hS : (∑ a : (ZMod q)ˣ, F (a:ZMod q)) = ∑ a∈S, F a := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
      (t := S) (fun a _ => (a : ZMod q))
    · intro a _
      simp [S,a.isUnit]
    · intro a _ b _ h
      exact Units.ext h
    · intro a ha
      have hu : IsUnit a := by simpa [S] using ha
      exact ⟨hu.unit,Finset.mem_univ _,hu.unit_spec⟩
    · intro a _
      rfl
  rw [hS]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hnot
  have hn : ¬ IsUnit a := by simpa [S] using hnot
  dsimp [F]
  simp [MulChar.map_nonunit _ hn]

/-- The common modulus is a multiple of the LCM of the primitive levels.
All coefficients are those of the actual finite additiveWeight expansion. -/
theorem liftedContinuousPacket_bound {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    (χ : DirichletCharacter ℂ d₁) (ψ : DirichletCharacter ℂ d₂)
    (L M : ℕ) (hL : 0 < L) (h₁ : d₁∣L) (h₂ : d₂∣L)
    (S : Finset ℕ) (hS : S ⊆ Icc 1 M)
    (U X β₁ γ₁ β₂ γ₂ : ℝ) (hU : 0≤U) (hX : 0≤X)
    (hβ₁ : 1/2≤β₁) (hβ₂ : 1/2≤β₂) (n : ℕ) :
    let a (m : ℕ) : ℂ :=
      if hm : 0 < m then
        letI : NeZero (L*m) := ⟨(Nat.mul_pos hL hm).ne'⟩
        canonicalPairCoefficient
          (DirichletCharacter.changeLevel (h₁.trans (dvd_mul_right L m)) χ)
          (DirichletCharacter.changeLevel (h₂.trans (dvd_mul_right L m)) ψ)
          (fun a => ZMod.stdAddChar (-(n:ZMod (L*m))*(a:ZMod (L*m))))
      else 0
    ‖(X:ℂ)*(∑ m∈S, a m * pairIntegral β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ)))‖ ≤
      8*exceptionalWeightConstant*X*U/(L.totient:ℝ) := by
  dsimp only
  let g := Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ)
  have hg : 0≤g := by dsimp [g]; positivity
  have hgL : g≤(L:ℝ) := by
    calc
      g ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul
          (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hL h₁))
          (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hL h₂))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  apply continuousPacket_bound S M L hL hS g U X β₁ γ₁ β₂ γ₂ hg hgL hU hX hβ₁ hβ₂
  intro m hm
  have hm0 : 0 < m := (mem_Icc.mp (hS hm)).1
  rw [dif_pos hm0]
  letI : NeZero (L*m) := ⟨(Nat.mul_pos hL hm0).ne'⟩
  have h := canonicalPairCoefficient_bound
    (DirichletCharacter.changeLevel (h₁.trans (dvd_mul_right L m)) χ)
    (DirichletCharacter.changeLevel (h₂.trans (dvd_mul_right L m)) ψ)
    (fun a => ZMod.stdAddChar (-(n:ZMod (L*m))*(a:ZMod (L*m))))
    (fun a => by
      have hu := AddChar.norm_apply (ZMod.stdAddChar (N := L*m))
        (-(n:ZMod (L*m))*(a:ZMod (L*m)))
      exact hu.le)
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel] at h
  apply h.trans
  unfold g
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos d₁) χ.conductor_dvd_level))
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos d₂) ψ.conductor_dvd_level))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.signedPair_eq
#print axioms InnerFloorGaussPacket.liftedContinuousPacket_bound
/-! Plancherel bridge adapted from ShortProgressionsMeanTheta (#3789),
and the verified InnerFloorPhysicalL2 research module. -/
section
open Set MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ContDiff BigOperators Interval
namespace InnerFloorZeroModel
noncomputable section
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in


private theorem test_fourier_swap {f : ℝ → ℂ} (hf : Integrable f) (g : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 f) x • g x) = ∫ x, f x • (𝓕 g) x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf g.integrable
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem ae_eq_of_schwartz_test {u v : ℝ → ℂ}
    (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume)
    (h : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * u x) = ∫ x, φ x * v x) :
    u =ᵐ[volume] v := by
  apply ae_eq_of_integral_contDiff_smul_eq hu hv
  intro g hg hgc
  let φ := (hgc.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  simp only [RCLike.real_smul_eq_coe_mul]
  exact h φ
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem lp_test (v : Lp ℂ 2 (volume : Measure ℝ)) (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 φ) x • v x) = ∫ x, φ x • (𝓕 v) x := calc
  _ = Lp.toTemperedDistribution v (𝓕 φ) := (Lp.toTemperedDistribution_apply ..).symm
  _ = (𝓕 (Lp.toTemperedDistribution v)) φ := rfl
  _ = Lp.toTemperedDistribution (𝓕 v) φ := by rw [Lp.fourier_toTemperedDistribution_eq]
  _ = _ := Lp.toTemperedDistribution_apply ..
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem fourier_agrees {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (𝓕 f) =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  let v := h₂.toLp f
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_schwartz_test hc.locallyIntegrable
    ((Lp.memLp (𝓕 v)).locallyIntegrable (by norm_num))
  intro φ
  have A := test_fourier_swap (f := f) h₁ φ
  have B := lp_test v φ
  simp only [smul_eq_mul] at A B
  have C : (∫ x : ℝ, f x * (𝓕 φ) x) = ∫ x : ℝ, (𝓕 φ) x * v x := by
    apply integral_congr_ae
    filter_upwards [h₂.coeFn_toLp] with x hx
    change f x * (𝓕 φ) x = (𝓕 φ) x * (h₂.toLp f) x
    rw [hx, mul_comm]
  have D : (∫ x : ℝ, φ x * (𝓕 f) x) = ∫ x : ℝ, (𝓕 f) x * φ x :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm ..)
  exact D.trans (A.trans (C.trans B))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem lp_energy (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ x, ‖f x‖^2 = ‖f‖^2 := by
  conv_rhs => rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  exact integral_congr_ae (ae_of_all _ fun x => norm_sq_eq_re_inner (𝕜 := ℂ) (f x))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem box_plancherel {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    Integrable (fun ξ => ‖𝓕 f ξ‖^2) ∧ (∫ ξ, ‖𝓕 f ξ‖^2) = ∫ x, ‖f x‖^2 := by
  let v := h₂.toLp f
  have he := fourier_agrees h₁ h₂
  have hae : (fun ξ => ‖𝓕 f ξ‖^2) =ᵐ[volume] (fun ξ => ‖(𝓕 v) ξ‖^2) := by
    filter_upwards [he] with ξ h using congrArg (fun z : ℂ => ‖z‖^2) h
  refine ⟨((Lp.memLp (𝓕 v)).norm.integrable_sq).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, lp_energy, Lp.norm_fourier_eq, ← lp_energy]
  apply integral_congr_ae
  filter_upwards [h₂.coeFn_toLp] with x h using congrArg (fun z : ℂ => ‖z‖^2) h

def zeroKernel (β γ : ℝ) : ℝ → ℂ :=
  (Set.Ioc (0:ℝ) 1).indicator (fun x => (x^(β-1):ℝ) • phase (γ*Real.log x))

private theorem kernel_norm_eq (β γ : ℝ) :
    (fun x => ‖zeroKernel β γ x‖) =
      (Set.Ioc (0:ℝ) 1).indicator (fun x => x^(β-1)) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
  · rw [zeroKernel,Set.indicator_of_mem hx,Set.indicator_of_mem hx,norm_smul,norm_phase,
      mul_one,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
  · simp [zeroKernel,Set.indicator_of_notMem hx]

private theorem kernel_sq_eq (β γ : ℝ) :
    (fun x => ‖zeroKernel β γ x‖^2) =
      (Set.Ioc (0:ℝ) 1).indicator (fun x => x^(2*β-2)) := by
  funext x
  have hn := congrFun (kernel_norm_eq β γ) x
  rw [hn]
  by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
  · rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx,
      ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    congr 1
    norm_num
    ring
  · simp [Set.indicator_of_notMem hx]

private theorem kernel_integrable (β γ : ℝ) (hβ : 0 < β) :
    Integrable (zeroKernel β γ) := by
  have hm : Measurable (zeroKernel β γ) := by
    unfold zeroKernel
    apply Measurable.indicator _ measurableSet_Ioc
    unfold phase
    fun_prop
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  rw [kernel_norm_eq,integrable_indicator_iff measurableSet_Ioc]
  exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β-1)).1

private theorem kernel_memLp (β γ : ℝ) (hβ : 1/2 < β) :
    MemLp (zeroKernel β γ) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (kernel_integrable β γ (by linarith)).aestronglyMeasurable).mpr
  rw [kernel_sq_eq,integrable_indicator_iff measurableSet_Ioc]
  exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 2*β-2)).1

private theorem kernel_energy (β γ : ℝ) (hβ : 1/2 < β) :
    ∫ x, ‖zeroKernel β γ x‖^2 = 1/(2*β-1) := by
  rw [kernel_sq_eq,integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),
    integral_rpow (Or.inl (by linarith : -1 < 2*β-2))]
  rw [show 2*β-2+1=2*β-1 by ring,Real.one_rpow,
    Real.zero_rpow (by linarith : 2*β-1≠0),sub_zero]

private theorem transform_fourier (β γ v : ℝ) :
    transform β γ v = 𝓕 (zeroKernel β γ) (-v) := by
  rw [Real.fourier_real_eq_integral_exp_smul,transform,
    intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
  have he : (fun x => Complex.exp (↑(-2*Real.pi*x*(-v))*Complex.I) • zeroKernel β γ x) =
    (Set.Ioc (0:ℝ) 1).indicator (fun x => (x^(β-1):ℝ) • phase (γ*Real.log x+2*Real.pi*v*x)) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
    · rw [zeroKernel,Set.indicator_of_mem hx,Set.indicator_of_mem hx]
      simp only [smul_eq_mul,phase,Complex.ofReal_add,add_mul,Complex.exp_add,
        RCLike.real_smul_eq_coe_mul]
      rw [show (-2*Real.pi*x*(-v)) = 2*Real.pi*v*x by ring]
      ring
    · simp [zeroKernel,Set.indicator_of_notMem hx]
  rw [he,integral_indicator measurableSet_Ioc]

theorem transform_energy (β γ : ℝ) (hβ : 1/2 < β) :
    Integrable (fun v => ‖transform β γ v‖^2) ∧
      (∫ v, ‖transform β γ v‖^2) = 1/(2*β-1) := by
  obtain ⟨hi,he⟩ := box_plancherel (kernel_integrable β γ (by linarith))
    (kernel_memLp β γ hβ)
  simp_rw [transform_fourier]
  constructor
  · simpa only [neg_one_mul] using hi.comp_mul_left' (by norm_num : (-1:ℝ)≠0)
  · calc
      _ = (∫ v, ‖𝓕 (zeroKernel β γ) v‖^2) := by
        have h := Measure.integral_comp_mul_left (fun v => ‖𝓕 (zeroKernel β γ) v‖^2) (-1:ℝ)
        simpa [neg_one_mul] using h
      _ = _ := he.trans (kernel_energy β γ hβ)


/-- The absolute integral of a pair is uniformly bounded at every cutoff,
including the long inner arcs. No hypothesis on the imaginary parts. -/
theorem pairIntegral_uniform (β₁ γ₁ β₂ γ₂ R : ℝ)
    (h₁ : 3/4≤β₁) (h₂ : 3/4≤β₂) (hR : 0≤R) :
    ‖pairIntegral β₁ γ₁ β₂ γ₂ R‖ ≤ 2 := by
  obtain ⟨hi₁,he₁⟩ := transform_energy β₁ γ₁ (by linarith)
  obtain ⟨hi₂,he₂⟩ := transform_energy β₂ γ₂ (by linarith)
  let f (v : ℝ) := (‖transform β₁ γ₁ v‖^2+‖transform β₂ γ₂ v‖^2)/2
  have hf : Integrable f := (hi₁.add hi₂).div_const 2
  have hp (v : ℝ) :
      ‖transform β₁ γ₁ v * transform β₂ γ₂ v * phase (-(2*Real.pi*v))‖ ≤ f v := by
    rw [norm_mul,norm_mul,norm_phase,mul_one]
    dsimp [f]
    nlinarith [sq_nonneg (‖transform β₁ γ₁ v‖-‖transform β₂ γ₂ v‖)]
  have hA : ∀ v, 0≤f v := by intro v;dsimp [f];positivity
  unfold pairIntegral
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  calc
    _ ≤ ∫ v in Ioc (-R) R,
      ‖transform β₁ γ₁ v * transform β₂ γ₂ v * phase (-(2*Real.pi*v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioc (-R) R, f v :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hf.integrableOn (Filter.Eventually.of_forall hp)
    _ ≤ ∫ v, f v := setIntegral_le_integral hf (Filter.Eventually.of_forall hA)
    _ = (1/(2*β₁-1)+1/(2*β₂-1))/2 := by
      dsimp [f]
      rw [integral_div,integral_add hi₁ hi₂,he₁,he₂]
    _ ≤ 2 := by
      have hb₁ : 1/(2*β₁-1) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
      have hb₂ : 1/(2*β₂-1) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
      linarith

end
end InnerFloorZeroModel
#print axioms InnerFloorZeroModel.transform_energy

#print axioms InnerFloorZeroModel.pairIntegral_uniform
end

namespace DyadicMixedB4CharacterFactorBound
noncomputable section
theorem norm_gauss_neg_shift_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-x))‖ ≤ ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ := by
  have equality : ZMod.stdAddChar.mulShift (-x) =
      (ZMod.stdAddChar.mulShift x).mulShift ((-1 : (ZMod q)ˣ) : ZMod q) := by
    ext y
    simp [AddChar.mulShift_apply, mul_assoc]
  rw [equality, gaussSum_mulShift_eq χ (ZMod.stdAddChar.mulShift x) (-1), norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)


end
end DyadicMixedB4CharacterFactorBound

open InnerFloorLinearTotient

/-!
A product-conductor saving for arbitrary shifts, including noncoprime
shifts. The low-product-conductor packet is kept separate.
-/
open Finset
open scoped Classical
open DyadicMixedB4CharacterFactorBound
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem divisorSum_le_log (m : ℕ) (hm : 0 < m) :
    (∑ f ∈ m.divisors, (f:ℝ)) ≤ (m:ℝ)*(1+Real.log m) := by
  have hsub : m.divisors ⊆ Icc 1 m := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)⟩
  have hh : (∑ i∈Icc 1 m,(i:ℝ)⁻¹) ≤ 1+Real.log m := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      using harmonic_le_one_add_log m
  calc
    _ = ∑ ab∈m.divisorsAntidiagonal,(ab.1:ℝ) := by
      rw [Nat.sum_divisorsAntidiagonal (fun a _ => (a:ℝ))]
    _ = ∑ ab∈m.divisorsAntidiagonal,(m:ℝ)*(ab.2:ℝ)⁻¹ := by
      apply sum_congr rfl
      intro ab hab
      have hp := (Nat.mem_divisorsAntidiagonal.mp hab).1
      have hb : ab.2 ≠ 0 := by
        intro hb
        rw [hb,mul_zero] at hp
        omega
      have he : (ab.1:ℝ)*(ab.2:ℝ)=(m:ℝ) := by exact_mod_cast hp
      rw [← he]
      field_simp
    _ = (m:ℝ)*(∑ f∈m.divisors,(f:ℝ)⁻¹) := by
      rw [← mul_sum,Nat.sum_divisorsAntidiagonal' (fun _ b => (b:ℝ)⁻¹)]
    _ ≤ (m:ℝ)*(∑ f∈Icc 1 m,(f:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)

variable {q : ℕ} [NeZero q]

/-- Even when the shift is not invertible modulo q, the shifted Gauss sum
is at most q (1+log q) / sqrt(conductor). -/
theorem shiftedGauss_productConductor (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*(1+Real.log q)/Real.sqrt χ.conductor := by
  let d := χ.conductor
  have hd : d ∣ q := χ.conductor_dvd_level
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd (NeZero.pos q)
  obtain ⟨m,hm⟩ := hd
  have hmp : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm0,mul_zero] at hm
    exact (NeZero.ne q) hm
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hdp
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hmp
  have hqR : (q:ℝ)=(d:ℝ)*(m:ℝ) := by exact_mod_cast hm
  have hsub : n.divisors.filter (fun f => d*f ∣ q) ⊆ m.divisors := by
    intro f hf
    have hdiv := (mem_filter.mp hf).2
    rw [hm] at hdiv
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left hdp hdiv,hmp.ne'⟩
  have hmq : m ≤ q := by
    rw [hm]
    exact Nat.le_mul_of_pos_left _ hdp
  have hlog : Real.log m≤Real.log q :=
    Real.log_le_log hmR (by exact_mod_cast hmq)
  have hs : (Real.sqrt (d:ℝ))^2=(d:ℝ) := Real.sq_sqrt hdR.le
  have hroot : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 hdR
  calc
    _ ≤ Real.sqrt d*(∑ f∈n.divisors.filter (fun f => d*f ∣ q),(f:ℝ)) :=
      (norm_gauss_neg_shift_le χ (n:ZMod q)).trans
        (by simpa only [DirichletCharacter.changeLevel_self,d] using
          norm_dirichlet_gauss_induced (dvd_refl q) χ n hn)
    _ ≤ Real.sqrt d*(∑ f∈m.divisors,(f:ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((m:ℝ)*(1+Real.log m)) :=
      mul_le_mul_of_nonneg_left (divisorSum_le_log m hmp) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((m:ℝ)*(1+Real.log q)) := by gcongr
    _ = _ := by
      change Real.sqrt (d:ℝ)*((m:ℝ)*(1+Real.log q)) =
        (q:ℝ)*(1+Real.log q)/Real.sqrt (d:ℝ)
      apply (eq_div_iff hroot.ne').2
      calc
        _ = (Real.sqrt (d:ℝ))^2 * ((m:ℝ)*(1+Real.log q)) := by ring
        _ = (d:ℝ)*((m:ℝ)*(1+Real.log q)) := by rw [hs]
        _ = _ := by rw [hqR]; ring

/-- The high-product-conductor part of the signed quadratic form has a
uniform square-root saving, independent of gcd(n,q). -/
theorem highProductConductorPacketBound
    (n : ℕ) (hn : 0 < n) (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) (D : ℕ) (hD : 0 < D) :
    ‖∑ χ∈S, ∑ ψ∈S.filter (fun ψ => D≤(χ*ψ).conductor),
       (w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      ((q:ℝ)*(1+Real.log q)/Real.sqrt D)*(∑ χ∈S,‖w χ‖)^2 := by
  let K := (q:ℝ)*(1+Real.log q)/Real.sqrt D
  have hq1 : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hL : 0≤(q:ℝ)*(1+Real.log q) := by
    have := Real.log_nonneg hq1
    positivity
  have hK : 0≤K := div_nonneg hL (Real.sqrt_nonneg _)
  have hterm (χ ψ : DirichletCharacter ℂ q) (hψ : D≤(χ*ψ).conductor) :
      ‖(w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
        ‖w χ‖*‖w ψ‖*K := by
    simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (shiftedGauss_productConductor (χ*ψ) n hn).trans
    exact div_le_div_of_nonneg_left hL (Real.sqrt_pos.2 (by exact_mod_cast hD))
      (Real.sqrt_le_sqrt (by exact_mod_cast hψ))
  change _ ≤ K*(∑ χ∈S,‖w χ‖)^2
  calc
    _ ≤ ∑ χ∈S, ∑ ψ∈S.filter (fun ψ => D≤(χ*ψ).conductor), ‖w χ‖*‖w ψ‖*K := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro χ _
      apply (norm_sum_le _ _).trans
      exact sum_le_sum fun ψ hψ => hterm χ ψ (mem_filter.mp hψ).2
    _ ≤ ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*K :=
      sum_le_sum fun χ _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

end
end InnerFloorResearch

open InnerFloorLinearTotient

/-!
Aggregate high-product-conductor weights over all common multiples.
Only finite arithmetic and the verified Gauss bound are used.
-/
open Finset InnerFloorLinearTotient
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem commonMultipleTotientWeight (A L : ℕ) (hL : 0 < L) (hLA : L ≤ A) :
    (∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) ≤
      (weightConstant*(1+Real.log A))^2 := by
  let F (d : ℕ) : ℝ := if d=L then L else 0
  have hF : ∀ d, 0≤F d := by intro d; dsimp [F]; split_ifs <;> positivity
  have hA : 0 < A := hL.trans_le hLA
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by exact_mod_cast hA)
  have hlogL : Real.log L ≤ Real.log A :=
    Real.log_le_log (by exact_mod_cast hL) (by exact_mod_cast hLA)
  have hLf : L ∈ Icc 1 A := mem_Icc.mpr ⟨hL,hLA⟩
  have hratio : (L:ℝ)/(L.totient:ℝ) ≤ weightConstant*(1+Real.log A) :=
    (ratio_totient_le L hL).trans (mul_le_mul_of_nonneg_left (by linarith)
      weightConstant_nonneg)
  have hrewrite :
      (∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) =
      ∑ q ∈ Icc 1 A, (∑ d ∈ q.divisors,F d)/(q.totient:ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro q hq
    have hq0 : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
    have hmem : L ∈ q.divisors ↔ L ∣ q := by simp [Nat.mem_divisors,hq0]
    by_cases hdiv : L ∣ q
    · have h := hmem.mpr hdiv
      simp [F,hdiv,h]
    · have h : L ∉ q.divisors := fun hm => hdiv (hmem.mp hm)
      simp [F,hdiv,h]
  have hsum : (∑ d ∈ Icc 1 A,F d/(d.totient:ℝ)) = (L:ℝ)/(L.totient:ℝ) := by
    simp [F,ite_div,hLf]
  rw [hrewrite]
  apply (sum_conductor_weights A F hF).trans
  rw [hsum,pow_two]
  exact mul_le_mul_of_nonneg_right hratio (mul_nonneg weightConstant_nonneg (by linarith))

def productCoefficient (q d₁ d₂ D : ℕ) : ℝ :=
  Real.sqrt d₁ * Real.sqrt d₂ * q * (1+Real.log q) /
    ((q.totient:ℝ)^2 * Real.sqrt D)

/-- At most four logarithms are lost when summing the high-product
conductor coefficient over all moduli divisible by both original
conductors. No assumption on gcd(n,q) occurs. -/
theorem productCoefficientFamily (A d₁ d₂ D : ℕ)
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (hD : 0 < D) :
    (∑ q ∈ (Icc 1 A).filter (fun q => d₁ ∣ q ∧ d₂ ∣ q),
       productCoefficient q d₁ d₂ D) ≤
      weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  let L := Nat.lcm d₁ d₂
  have hL : 0 < L := Nat.lcm_pos h₁ h₂
  have hset :
      (Icc 1 A).filter (fun q => d₁ ∣ q ∧ d₂ ∣ q) =
        (Icc 1 A).filter (fun q => L ∣ q) := by
    ext q
    simp [L,Nat.lcm_dvd_iff]
  have hD' : 0 < Real.sqrt (D:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hD)
  have hd₁ : d₁ ≤ L := Nat.le_of_dvd hL (Nat.dvd_lcm_left d₁ d₂)
  have hd₂ : d₂ ≤ L := Nat.le_of_dvd hL (Nat.dvd_lcm_right d₁ d₂)
  have hroot : Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ) ≤ (L:ℝ) := by
    calc
      _ ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hd₁))
          (Real.sqrt_le_sqrt (by exact_mod_cast hd₂)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  by_cases hLA : L≤A
  · have hA : 0 < A := hL.trans_le hLA
    have hlogA : 0≤Real.log A := Real.log_nonneg (by exact_mod_cast hA)
    let C := weightConstant*(1+Real.log A)^2/Real.sqrt D
    have hC : 0≤C := by
      dsimp [C]
      exact div_nonneg (mul_nonneg weightConstant_nonneg (sq_nonneg _)) (Real.sqrt_nonneg _)
    have ht (q : ℕ) (hq : q∈(Icc 1 A).filter (fun q => L ∣ q)) :
        productCoefficient q d₁ d₂ D ≤ C*((L:ℝ)/(q.totient:ℝ)) := by
      have hq1 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hqA := (mem_Icc.mp (mem_filter.mp hq).1).2
      have hlogq : 0≤Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
      have hlog : Real.log q≤Real.log A :=
        Real.log_le_log (by exact_mod_cast hq1) (by exact_mod_cast hqA)
      have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
      have hr : (q:ℝ)/(q.totient:ℝ) ≤ weightConstant*(1+Real.log A) :=
        (ratio_totient_le q hq1).trans
          (mul_le_mul_of_nonneg_left (by linarith) weightConstant_nonneg)
      calc
        _ = (Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ)/(q.totient:ℝ))*
            ((q:ℝ)/(q.totient:ℝ))*(1+Real.log q)/Real.sqrt D := by
          unfold productCoefficient
          ring
        _ ≤ ((L:ℝ)/(q.totient:ℝ))*(weightConstant*(1+Real.log A))*
            (1+Real.log A)/Real.sqrt D := by
          apply div_le_div_of_nonneg_right _ hD'.le
          apply mul_le_mul _ (by linarith) (by positivity)
            (mul_nonneg (by positivity) (mul_nonneg weightConstant_nonneg (by linarith)))
          exact mul_le_mul (div_le_div_of_nonneg_right hroot hφ.le) hr
            (by positivity) (by positivity)
        _ = _ := by dsimp [C]; ring
    rw [hset]
    calc
      _ ≤ ∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), C*((L:ℝ)/(q.totient:ℝ)) :=
        sum_le_sum ht
      _ = C*(∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) :=
        (mul_sum ..).symm
      _ ≤ C*(weightConstant*(1+Real.log A))^2 :=
        mul_le_mul_of_nonneg_left (commonMultipleTotientWeight A L hL hLA) hC
      _ = _ := by dsimp [C]; ring
  · have he : (Icc 1 A).filter (fun q => L ∣ q)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hq' := mem_filter.mp hq
      exact hLA ((Nat.le_of_dvd (mem_Icc.mp hq'.1).1 hq'.2).trans (mem_Icc.mp hq'.1).2)
    rw [hset,he,sum_empty]
    exact div_nonneg (mul_nonneg (pow_nonneg weightConstant_nonneg _) (by positivity)) (Real.sqrt_nonneg _)

end
end InnerFloorResearch

open InnerFloorLinearTotient

/-!
Retain both the product conductor and the gcd of the shift with the
imprimitive part of the modulus. All estimates are unconditional.
-/
open Finset DyadicMixedB4CharacterFactorBound
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

variable {q : ℕ} [NeZero q]

theorem shiftedGauss_gcdBound (χ : DirichletCharacter ℂ q) (n : ℕ)
    (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt χ.conductor * (Nat.gcd n (q/χ.conductor):ℝ) *
        (1+Real.log (Nat.gcd n (q/χ.conductor))) := by
  let d := χ.conductor
  have hd : d ∣ q := χ.conductor_dvd_level
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd (NeZero.pos q)
  obtain ⟨m,hm⟩ := hd
  have hmp : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm0,mul_zero] at hm
    exact (NeZero.ne q) hm
  have hm' : q/d=m := by
    rw [hm,Nat.mul_comm,Nat.mul_div_cancel _ hdp]
  let g := Nat.gcd n m
  have hgp : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hsub : n.divisors.filter (fun f => d*f ∣ q) ⊆ g.divisors := by
    intro f hf
    have hdiv := (mem_filter.mp hf).2
    rw [hm] at hdiv
    have hfm := Nat.dvd_of_mul_dvd_mul_left hdp hdiv
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd
      (Nat.dvd_of_mem_divisors (mem_filter.mp hf).1) hfm,hgp.ne'⟩
  change _ ≤ Real.sqrt d * (Nat.gcd n (q/d):ℝ) * _
  rw [hm']
  calc
    _ ≤ Real.sqrt d*(∑ f∈n.divisors.filter (fun f => d*f ∣ q),(f:ℝ)) :=
      (norm_gauss_neg_shift_le χ (n:ZMod q)).trans
        (by simpa only [DirichletCharacter.changeLevel_self,d] using
          norm_dirichlet_gauss_induced (dvd_refl q) χ n hn)
    _ ≤ Real.sqrt d*(∑ f∈g.divisors,(f:ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((g:ℝ)*(1+Real.log g)) :=
      mul_le_mul_of_nonneg_left (divisorSum_le_log g hgp) (Real.sqrt_nonneg _)
    _ = _ := by dsimp [g,d]; ring

/-- A general bound using gcd(n,q) rather than the full modulus, useful
for small product conductor. -/
theorem shiftedGauss_smallProduct (χ : DirichletCharacter ℂ q) (n D : ℕ)
    (hn : 0 < n) (hD : χ.conductor ≤ D) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt D*(Nat.gcd n q:ℝ)*(1+Real.log q) := by
  let g := Nat.gcd n (q/χ.conductor)
  have hgp : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hgg : g ∣ Nat.gcd n q := Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    ((Nat.gcd_dvd_right _ _).trans (Nat.div_dvd_of_dvd χ.conductor_dvd_level))
  have hgq : g≤q := Nat.le_of_dvd (NeZero.pos q) (hgg.trans (Nat.gcd_dvd_right _ _))
  have hgg' : g≤Nat.gcd n q := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hn) hgg
  have hL : 0≤Real.log g := Real.log_nonneg (by exact_mod_cast hgp)
  have hl : Real.log (g:ℝ) ≤ Real.log (q:ℝ) :=
    Real.log_le_log (by exact_mod_cast hgp) (by exact_mod_cast hgq)
  calc
    _ ≤ Real.sqrt χ.conductor*(g:ℝ)*(1+Real.log g) :=
      shiftedGauss_gcdBound χ n hn
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hD))
          (by exact_mod_cast hgg' : (g:ℝ) ≤ (Nat.gcd n q:ℝ)) (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      · linarith
      · linarith
      · positivity

/-- The low-product-conductor part of a packet also has a saving when
gcd(n,q) is small. No coprimality assumption is necessary. -/
theorem lowProductGcdPacketBound (n : ℕ) (hn : 0 < n)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) (D : ℕ) :
    ‖∑ χ∈S, ∑ ψ∈S.filter (fun ψ => (χ*ψ).conductor≤D),
        (w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (Real.sqrt D*(Nat.gcd n q:ℝ)*(1+Real.log q))*(∑ χ∈S,‖w χ‖)^2 := by
  let K := Real.sqrt D*(Nat.gcd n q:ℝ)*(1+Real.log q)
  have hq1 : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hK : 0≤K := by
    dsimp [K]
    have := Real.log_nonneg hq1
    positivity
  have hterm (χ ψ : DirichletCharacter ℂ q) (hψ : (χ*ψ).conductor≤D) :
      ‖(w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
        ‖w χ‖*‖w ψ‖*K := by
    simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact shiftedGauss_smallProduct (χ*ψ) n D hn hψ
  change _ ≤ K*(∑ χ∈S,‖w χ‖)^2
  calc
    _ ≤ ∑ χ∈S, ∑ ψ∈S.filter (fun ψ => (χ*ψ).conductor≤D), ‖w χ‖*‖w ψ‖*K := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro χ _
      apply (norm_sum_le _ _).trans
      exact sum_le_sum fun ψ hψ => hterm χ ψ (mem_filter.mp hψ).2
    _ ≤ ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*K :=
      sum_le_sum fun χ _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring


/-- Interpolating the product conductor and gcd bounds eliminates the
conductor altogether. The ratio gcd(n,q)/q is the precise obstruction. -/
theorem shiftedGauss_geometricGcd (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q) := by
  let d := χ.conductor
  have hd : 0 < d := Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos q)
  have hs : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hL : 0 ≤ 1+Real.log q := by
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    linarith [Real.log_nonneg hq1]
  let a := ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖
  have ha : 0≤a := norm_nonneg _
  have h₁ : a ≤ (q:ℝ)*(1+Real.log q)/Real.sqrt d :=
    shiftedGauss_productConductor χ n hn
  have h₂ : a ≤ Real.sqrt d*(Nat.gcd n q:ℝ)*(1+Real.log q) :=
    shiftedGauss_smallProduct χ n d hn le_rfl
  have hsq : a^2 ≤ ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q)^2 := by
    calc
      _ = a*a := by ring
      _ ≤ ((q:ℝ)*(1+Real.log q)/Real.sqrt d)*
          (Real.sqrt d*(Nat.gcd n q:ℝ)*(1+Real.log q)) :=
        mul_le_mul h₁ h₂ ha (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hL) hs.le)
      _ = _ := by field_simp [hs.ne'] <;> ring
  have hroot : (Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ)))^2 =
      (q:ℝ)*(Nat.gcd n q:ℝ) := Real.sq_sqrt (by positivity)
  have hb : 0≤Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q) :=
    mul_nonneg (Real.sqrt_nonneg _) hL
  have hsq' : a^2 ≤ (Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q))^2 := by
    rw [mul_pow,hroot]
    exact hsq
  change a ≤ _
  nlinarith only [hsq',ha,hb]

/-- The fraction of a modulus accounted for by gcd(n,q) cannot increase
when q is replaced by a multiple. -/
theorem gcdRatio_mono_multiple (n L q : ℕ) (hn : 0 < n) (hL : 0 < L)
    (hLq : L ∣ q) (hq : 0 < q) :
    (Nat.gcd n q:ℝ)/(q:ℝ) ≤ (Nat.gcd n L:ℝ)/(L:ℝ) := by
  obtain ⟨m,hm⟩ := hLq
  have hmpos : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm,hm0,mul_zero] at hq
    omega
  let d := Nat.gcd n q
  have hd : d ∣ L*m := by rw [← hm]; exact Nat.gcd_dvd_right _ _
  have hsplit : d ∣ d.gcd L * d.gcd m := by
    simpa only [Nat.gcd_comm] using (Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr hd)
  have h₁ : d.gcd L ∣ Nat.gcd n L :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left n q))
      (Nat.gcd_dvd_right _ _)
  have h₂ : d.gcd m ∣ m := Nat.gcd_dvd_right _ _
  have hdiv : d ∣ Nat.gcd n L*m := hsplit.trans (Nat.mul_dvd_mul h₁ h₂)
  have hle : d ≤ Nat.gcd n L*m :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hn) hmpos) hdiv
  have hd' : (d:ℝ) ≤ (Nat.gcd n L:ℝ)*(m:ℝ) := by exact_mod_cast hle
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hm' : (q:ℝ)=(L:ℝ)*(m:ℝ) := by exact_mod_cast hm
  apply (div_le_div_iff₀ hq' hL').2
  calc
    _ ≤ ((Nat.gcd n L:ℝ)*(m:ℝ))*(L:ℝ) :=
      mul_le_mul_of_nonneg_right hd' hL'.le
    _ = _ := by rw [hm']; ring


end
end InnerFloorResearch

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open DyadicMixedB4CharacterFactorBound
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
variable {q : ℕ} [NeZero q]

def signedCoefficient (χ ψ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  canonicalPairCoefficient χ ψ (fun a => ZMod.stdAddChar (-(n:ZMod q)*(a:ZMod q)))

/-- Isolate the conductor factors of the two actual Fourier weights.
The third Gauss sum retains the signed information. -/
theorem signedCoefficient_norm_le (χ ψ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖signedCoefficient χ ψ n‖ ≤
      Real.sqrt χ.conductor * Real.sqrt ψ.conductor *
        ‖gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ /
          (q.totient:ℝ)^2 := by
  have h₁ := norm_dirichlet_gauss_standard χ⁻¹
  have h₂ := norm_dirichlet_gauss_standard ψ⁻¹
  rw [DirichletCharacter.conductor_inv] at h₁ h₂
  rw [signedCoefficient,signedPair_eq,norm_mul,norm_div,norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (Real.sqrt χ.conductor * Real.sqrt ψ.conductor / (q.totient:ℝ)^2) *
        ‖gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul h₁ h₂ (norm_nonneg _) (Real.sqrt_nonneg _)) (sq_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

/-- Real high-product-conductor estimate with no coprimality restriction. -/
theorem signedCoefficient_highProduct (χ ψ : DirichletCharacter ℂ q)
    (n D : ℕ) (hn : 0 < n) (hDpos : 0 < D) (hD : D ≤ (χ*ψ).conductor) :
    ‖signedCoefficient χ ψ n‖ ≤ productCoefficient q χ.conductor ψ.conductor D := by
  apply (signedCoefficient_norm_le χ ψ n).trans
  unfold productCoefficient
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hlog : 0≤1+Real.log q := by linarith [Real.log_nonneg hq]
  have h := shiftedGauss_productConductor (χ*ψ) n hn
  have hden : 0 < Real.sqrt (D:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hDpos)
  have hshift : ‖gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*(1+Real.log q)/Real.sqrt D :=
    h.trans (div_le_div_of_nonneg_left (by positivity) hden
      (Real.sqrt_le_sqrt (by exact_mod_cast hD)))
  calc
    _ ≤ Real.sqrt χ.conductor*Real.sqrt ψ.conductor*
        ((q:ℝ)*(1+Real.log q)/Real.sqrt D)/(q.totient:ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hshift (by positivity)) (sq_nonneg _)
    _ = _ := by ring

end
end InnerFloorGaussPacket

#print axioms InnerFloorGaussPacket.signedCoefficient_norm_le
#print axioms InnerFloorGaussPacket.signedCoefficient_highProduct

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open DyadicMixedB4CharacterFactorBound
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

/-- Uniform product conductor under common lift. -/
theorem productConductor_changeLevel {L q : ℕ} [NeZero L] [NeZero q]
    (h : L∣q) (χ ψ : DirichletCharacter ℂ L) :
    (DirichletCharacter.changeLevel h χ * DirichletCharacter.changeLevel h ψ).conductor =
      (χ*ψ).conductor := by
  rw [← map_mul,DirichletCharacter.conductor_changeLevel]

/-- A finite common-multiple sum of the genuine signed coefficients times
continuous zero-pair integrals. Large product conductor gives a saving
even when the individual primitive levels are small. -/
theorem highProduct_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (β₁ γ₁ β₂ γ₂ : ℝ) (hβ₁ : 3/4≤β₁) (hβ₂ : 3/4≤β₂)
    (R : ℕ→ℝ) (hR : ∀ q∈S,0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * pairIntegral β₁ γ₁ β₂ γ₂ (R q)‖ ≤
      2*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  dsimp only
  let c (q : ℕ) := productCoefficient q χ.conductor ψ.conductor D
  have hc (q : ℕ) (hq : q∈S) :
      ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0)‖ ≤ c q := by
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    have hq0 : 0 < q := (mem_Icc.mp hqR).1
    rw [dif_pos ⟨hq0,hqL⟩]
    letI : NeZero q := ⟨hq0.ne'⟩
    have hp : D ≤ (DirichletCharacter.changeLevel hqL χ *
          DirichletCharacter.changeLevel hqL ψ).conductor := by
      rw [productConductor_changeLevel]
      exact hprod
    have h := signedCoefficient_highProduct
      (DirichletCharacter.changeLevel hqL χ) (DirichletCharacter.changeLevel hqL ψ) n D hn hD hp
    simpa only [c,DirichletCharacter.conductor_changeLevel] using h
  have hS' : S ⊆ (Icc 1 A).filter (fun q => χ.conductor∣q ∧ ψ.conductor∣q) := by
    intro q hq
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    exact mem_filter.mpr ⟨hqR,χ.conductor_dvd_level.trans hqL,ψ.conductor_dvd_level.trans hqL⟩
  have hsum : ∑ q∈S,c q ≤ weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
    apply (sum_le_sum_of_subset_of_nonneg hS' (fun q hq _ => ?_)).trans
      (productCoefficientFamily A χ.conductor ψ.conductor D
        (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos L))
        (Nat.pos_of_dvd_of_pos ψ.conductor_dvd_level (NeZero.pos L)) hD)
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hq0
    have hlog := Real.log_nonneg hq1
    unfold productCoefficient
    positivity
  calc
    _ ≤ ∑ q∈S, ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0) *
        pairIntegral β₁ γ₁ β₂ γ₂ (R q)‖ := norm_sum_le _ _
    _ ≤ ∑ q∈S,c q*2 := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul (hc q hq) (pairIntegral_uniform β₁ γ₁ β₂ γ₂ (R q) hβ₁ hβ₂ (hR q hq))
        (norm_nonneg _) ((norm_nonneg _).trans (hc q hq))
    _ ≤ _ := by
      rw [← sum_mul]
      calc
        _ ≤ (weightConstant^3*(1+Real.log A)^4/Real.sqrt D)*2 :=
          mul_le_mul_of_nonneg_right hsum (by norm_num)
        _ = _ := by ring

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.productConductor_changeLevel
#print axioms InnerFloorGaussPacket.highProduct_sum

section
open Set MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ContDiff BigOperators Interval
namespace InnerFloorZeroModel
noncomputable section
/-- Exactly the trapezoid used in the accepted canonical explicit formula. -/
def dyadicTaper (a b x : ℝ) : ℝ := max 0 (min (x-a) (min 1 (b+1-x)))

theorem dyadicTaper_bounds (a b x : ℝ) :
    0 ≤ dyadicTaper a b x ∧ dyadicTaper a b x ≤ 1 := by
  unfold dyadicTaper
  exact ⟨le_max_left _ _,max_le (by norm_num) ((min_le_right ..).trans (min_le_left ..))⟩

def dyadicKernel (a b : ℝ) (ρ : ℂ) : ℝ → ℂ :=
  (Ioc a (b+1)).indicator (fun x => (dyadicTaper a b x:ℂ)*(x:ℂ)^(ρ-1))

def dyadicTransform (a b : ℝ) (ρ : ℂ) (v : ℝ) : ℂ :=
  ∫ x in a..b+1, (dyadicTaper a b x:ℂ)*phase (2*Real.pi*v*x)*(x:ℂ)^(ρ-1)

theorem dyadicTransform_fourier (a b : ℝ) (ρ : ℂ) (v : ℝ)
    (hab : a ≤ b+1) :
    dyadicTransform a b ρ v = 𝓕 (dyadicKernel a b ρ) (-v) := by
  rw [Real.fourier_real_eq_integral_exp_smul,dyadicTransform,intervalIntegral.integral_of_le hab]
  have he : (fun x => Complex.exp (↑(-2*Real.pi*x*(-v))*Complex.I) • dyadicKernel a b ρ x) =
    (Ioc a (b+1)).indicator (fun x => (dyadicTaper a b x:ℂ)*phase (2*Real.pi*v*x)*(x:ℂ)^(ρ-1)) := by
    funext x
    by_cases hx : x∈Ioc a (b+1)
    · rw [dyadicKernel,Set.indicator_of_mem hx,Set.indicator_of_mem hx]
      simp only [smul_eq_mul,phase]
      rw [show (-2*Real.pi*x*(-v))=2*Real.pi*v*x by ring]
      ring
    · simp [dyadicKernel,Set.indicator_of_notMem hx]
  rw [he,integral_indicator measurableSet_Ioc]

theorem dyadicTransform_energy (a b N : ℝ) (ρ : ℂ)
    (ha : 0<a) (hab : a≤b+1) (hN : b+1≤N) (hρ : 1/2<ρ.re) :
    Integrable (fun v => ‖dyadicTransform a b ρ v‖^2) ∧
      (∫ v, ‖dyadicTransform a b ρ v‖^2) ≤ N^(2*ρ.re-1)/(2*ρ.re-1) := by
  let f (x : ℝ) : ℂ := (dyadicTaper a b x:ℂ)*(x:ℂ)^(ρ-1)
  have hcont : ContinuousOn f (Icc a (b+1)) := by
    intro x hx
    have hx0 : 0<x := ha.trans_le hx.1
    have ht : Continuous (fun x : ℝ => dyadicTaper a b x) := by unfold dyadicTaper;fun_prop
    exact ((Complex.continuous_ofReal.comp ht).continuousAt.mul
      (differentiableAt_id.ofReal_cpow_const (ρ-1) hx0.ne').continuousAt).continuousWithinAt
  have hf : IntegrableOn f (Ioc a (b+1)) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hfsq : IntegrableOn (fun x => ‖f x‖^2) (Ioc a (b+1)) :=
    (hcont.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hki : Integrable (dyadicKernel a b ρ) := by
    rw [dyadicKernel,integrable_indicator_iff measurableSet_Ioc]
    exact hf
  have hksq : (fun x => ‖dyadicKernel a b ρ x‖^2) =
      (Ioc a (b+1)).indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x∈Ioc a (b+1) <;> simp [dyadicKernel,f,hx]
  have hk₂ : MemLp (dyadicKernel a b ρ) 2 :=
    (memLp_two_iff_integrable_sq_norm hki.aestronglyMeasurable).mpr (by
      rw [hksq,integrable_indicator_iff measurableSet_Ioc];exact hfsq)
  obtain ⟨hi,he⟩ := box_plancherel hki hk₂
  have hpow (x : ℝ) (hx : x∈Ioc a (b+1)) :
      ‖f x‖^2 ≤ x^(2*ρ.re-2) := by
    have hx0 : 0<x := ha.trans hx.1
    have ht := dyadicTaper_bounds a b x
    dsimp [f]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0,Complex.sub_re,Complex.one_re]
    calc
      _ ≤ (x^(ρ.re-1))^2 :=
        pow_le_pow_left₀ (mul_nonneg ht.1 (Real.rpow_nonneg hx0.le _))
          (mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) ht.2) 2
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hx0.le]
        congr 1
        norm_num
        ring
  have hN0 : 0<N := ha.trans_le (hab.trans hN)
  have hp : IntegrableOn (fun x : ℝ => x^(2*ρ.re-2)) (Ioc 0 N) := by
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<2*ρ.re-2)).1
  have hsub : Ioc a (b+1) ⊆ Ioc 0 N :=
    fun x hx => ⟨ha.trans hx.1,hx.2.trans hN⟩
  have hfull : ∫ x, ‖dyadicKernel a b ρ x‖^2 ≤ N^(2*ρ.re-1)/(2*ρ.re-1) := by
    rw [hksq,integral_indicator measurableSet_Ioc]
    calc
      _ ≤ ∫ x in Ioc a (b+1), x^(2*ρ.re-2) :=
        setIntegral_mono_on hfsq (hp.mono_set hsub) measurableSet_Ioc hpow
      _ ≤ ∫ x in Ioc 0 N, x^(2*ρ.re-2) :=
        setIntegral_mono_set hp (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact Real.rpow_nonneg hx.1.le _) (Filter.Eventually.of_forall hsub)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hN0.le,
          integral_rpow (Or.inl (by linarith : -1<2*ρ.re-2)),
          show 2*ρ.re-2+1=2*ρ.re-1 by ring,Real.zero_rpow (by linarith : 2*ρ.re-1≠0),sub_zero]
  simp_rw [dyadicTransform_fourier a b ρ _ hab]
  constructor
  · simpa only [neg_one_mul] using hi.comp_mul_left' (by norm_num : (-1:ℝ)≠0)
  · calc
      _ = ∫ v, ‖𝓕 (dyadicKernel a b ρ) v‖^2 := by
        have h := Measure.integral_comp_mul_left (fun v => ‖𝓕 (dyadicKernel a b ρ) v‖^2) (-1:ℝ)
        simpa [neg_one_mul] using h
      _ ≤ _ := he.trans_le hfull


/-- The actual dyadic tapered pair with arbitrary windows.
This also permits the principal term rho=1. -/
def dyadicPair (a b c d : ℝ) (ρ σ : ℂ) (R n : ℝ) : ℂ :=
  ∫ v in -R..R, dyadicTransform a b ρ v * dyadicTransform c d σ v *
    phase (-(2*Real.pi*n*v))

theorem dyadicPair_uniform (a b c d N : ℝ) (ρ σ : ℂ) (R n : ℝ)
    (ha : 0<a) (hb : a≤b+1) (hc : 0<c) (hd : c≤d+1)
    (hbN : b+1≤N) (hdN : d+1≤N) (hN : 1≤N) (hR : 0≤R)
    (hρ : 3/4≤ρ.re) (hρ1 : ρ.re≤1)
    (hσ : 3/4≤σ.re) (hσ1 : σ.re≤1) :
    ‖dyadicPair a b c d ρ σ R n‖ ≤ 2*N := by
  obtain ⟨hi₁,he₁⟩ := dyadicTransform_energy a b N ρ ha hb hbN (by linarith)
  obtain ⟨hi₂,he₂⟩ := dyadicTransform_energy c d N σ hc hd hdN (by linarith)
  have hscalar (t : ℝ) (h₁ : 3/4≤t) (h₂ : t≤1) :
      N^(2*t-1)/(2*t-1)≤2*N := by
    have ht : 0<2*t-1 := by linarith
    have hp : N^(2*t-1)≤N := by
      calc
        _ ≤ N^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
        _ = _ := Real.rpow_one _
    apply (div_le_iff₀ ht).2
    have h := mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*(2*t-1) by linarith) (by linarith : 0≤N)
    nlinarith only [hp,h]
  let f (v : ℝ) := (‖dyadicTransform a b ρ v‖^2+‖dyadicTransform c d σ v‖^2)/2
  have hf : Integrable f := (hi₁.add hi₂).div_const 2
  have hp (v : ℝ) :
      ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖≤f v := by
    rw [norm_mul,norm_mul,norm_phase,mul_one]
    dsimp [f]
    nlinarith [sq_nonneg (‖dyadicTransform a b ρ v‖-‖dyadicTransform c d σ v‖)]
  have hA : ∀ v,0≤f v := by intro v;dsimp [f];positivity
  unfold dyadicPair
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  calc
    _ ≤ ∫ v in Ioc (-R) R, ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioc (-R) R,f v :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hf.integrableOn (Filter.Eventually.of_forall hp)
    _ ≤ ∫ v,f v := setIntegral_le_integral hf (Filter.Eventually.of_forall hA)
    _ ≤ 2*N := by
      dsimp [f]
      rw [integral_div,integral_add hi₁ hi₂]
      linarith only [he₁.trans (hscalar ρ.re hρ hρ1), he₂.trans (hscalar σ.re hσ hσ1)]


end
end InnerFloorZeroModel
end

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
theorem boundedHighProduct_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 0≤N) (J : ℕ→ℂ) (hJ : ∀ q∈S, ‖J q‖≤2*N) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * J q‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  dsimp only
  let c (q : ℕ) := productCoefficient q χ.conductor ψ.conductor D
  have hc (q : ℕ) (hq : q∈S) :
      ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0)‖ ≤ c q := by
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    have hq0 : 0 < q := (mem_Icc.mp hqR).1
    rw [dif_pos ⟨hq0,hqL⟩]
    letI : NeZero q := ⟨hq0.ne'⟩
    have hp : D ≤ (DirichletCharacter.changeLevel hqL χ *
          DirichletCharacter.changeLevel hqL ψ).conductor := by
      rw [productConductor_changeLevel]
      exact hprod
    have h := signedCoefficient_highProduct
      (DirichletCharacter.changeLevel hqL χ) (DirichletCharacter.changeLevel hqL ψ) n D hn hD hp
    simpa only [c,DirichletCharacter.conductor_changeLevel] using h
  have hS' : S ⊆ (Icc 1 A).filter (fun q => χ.conductor∣q ∧ ψ.conductor∣q) := by
    intro q hq
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    exact mem_filter.mpr ⟨hqR,χ.conductor_dvd_level.trans hqL,ψ.conductor_dvd_level.trans hqL⟩
  have hsum : ∑ q∈S,c q ≤ weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
    apply (sum_le_sum_of_subset_of_nonneg hS' (fun q hq _ => ?_)).trans
      (productCoefficientFamily A χ.conductor ψ.conductor D
        (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos L))
        (Nat.pos_of_dvd_of_pos ψ.conductor_dvd_level (NeZero.pos L)) hD)
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hq0
    have hlog := Real.log_nonneg hq1
    unfold productCoefficient
    positivity
  calc
    _ ≤ ∑ q∈S, ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0) *
        J q‖ := norm_sum_le _ _
    _ ≤ ∑ q∈S,c q*(2*N) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul (hc q hq) (hJ q hq)
        (norm_nonneg _) ((norm_nonneg _).trans (hc q hq))
    _ ≤ _ := by
      rw [← sum_mul]
      calc
        _ ≤ (weightConstant^3*(1+Real.log A)^4/Real.sqrt D)*(2*N) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
        _ = _ := by ring

/-- Exact taper-model version of the high-product packet estimate.
The radius and both dyadic windows may depend on the modulus. -/
theorem dyadicHighProduct_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hρ1 : ρ.re≤1) (hσ : 3/4≤σ.re) (hσ1 : σ.re≤1)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  apply boundedHighProduct_sum χ ψ A n D hn hD hprod S hS N (by linarith)
  intro q hq
  exact dyadicPair_uniform (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hρ1 hσ hσ1

end
end InnerFloorGaussPacket
#print axioms InnerFloorZeroModel.dyadicTransform_energy
#print axioms InnerFloorZeroModel.dyadicPair_uniform
#print axioms InnerFloorGaussPacket.boundedHighProduct_sum
#print axioms InnerFloorGaussPacket.dyadicHighProduct_sum

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open DyadicMixedB4CharacterFactorBound
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem shiftedGauss_commonRatio {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n L : ℕ) (hn : 0 < n)
    (hL : 0 < L) (hLq : L∣q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))*(1+Real.log q) := by
  have hq : 0 < q := NeZero.pos q
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hlog : 0≤1+Real.log q := by linarith [Real.log_nonneg hq1]
  have hratio := gcdRatio_mono_multiple n L q hn hL hLq hq
  let r := (Nat.gcd n L:ℝ)/(L:ℝ)
  have hr : 0≤r := by dsimp [r]; positivity
  have hsq : (q:ℝ)*(Nat.gcd n q:ℝ) ≤ (q:ℝ)^2*r := by
    have h := (div_le_iff₀ hqR).mp hratio
    change (Nat.gcd n q:ℝ) ≤ r*(q:ℝ) at h
    calc
      _ ≤ (q:ℝ)*(r*(q:ℝ)) := mul_le_mul_of_nonneg_left h hqR.le
      _ = _ := by ring
  have hs : Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ)) ≤ (q:ℝ)*Real.sqrt r := by
    calc
      _ ≤ Real.sqrt ((q:ℝ)^2*r) := Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hqR.le]
  exact (shiftedGauss_geometricGcd χ n hn).trans (mul_le_mul_of_nonneg_right hs hlog)

/-- The common-level coefficient has a square-root saving when only a small
fraction of that level divides n. This applies to any product conductor. -/
theorem signedCoefficient_commonRatio {L q : ℕ} [NeZero L] [NeZero q]
    (hLq : L∣q) (χ ψ : DirichletCharacter ℂ L) (n A : ℕ)
    (hn : 0 < n) (hqA : q≤A) :
    ‖signedCoefficient (DirichletCharacter.changeLevel hLq χ)
      (DirichletCharacter.changeLevel hLq ψ) n‖ ≤
      weightConstant*(1+Real.log A)^2*
      Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))*((L:ℝ)/(q.totient:ℝ)) := by
  have hq : 0 < q := NeZero.pos q
  have hL : 0 < L := NeZero.pos L
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hlogq := Real.log_nonneg hq1
  have hlog : Real.log q≤Real.log A :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqA)
  have hlogA : 0≤Real.log A := hlogq.trans hlog
  have hratio : (q:ℝ)/(q.totient:ℝ)≤weightConstant*(1+Real.log A) :=
    (ratio_totient_le q hq).trans
      (mul_le_mul_of_nonneg_left (by linarith) weightConstant_nonneg)
  have hdχ : χ.conductor≤L := Nat.le_of_dvd hL χ.conductor_dvd_level
  have hdψ : ψ.conductor≤L := Nat.le_of_dvd hL ψ.conductor_dvd_level
  have hroot : Real.sqrt χ.conductor * Real.sqrt ψ.conductor ≤ (L:ℝ) := by
    calc
      _ ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hdχ))
          (Real.sqrt_le_sqrt (by exact_mod_cast hdψ))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  let r := Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))
  have hr : 0≤r := Real.sqrt_nonneg _
  let C := DirichletCharacter.changeLevel hLq χ
  let P := DirichletCharacter.changeLevel hLq ψ
  have hb := signedCoefficient_norm_le C P n
  dsimp [C,P] at hb
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel] at hb
  have hshift := shiftedGauss_commonRatio (C*P) n L hn hL hLq
  calc
    _ ≤ _ := hb
    _ ≤ (L:ℝ)*((q:ℝ)*r*(1+Real.log q))/(q.totient:ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hroot hshift (norm_nonneg _) (Nat.cast_nonneg _)
    _ = ((L:ℝ)/(q.totient:ℝ))*((q:ℝ)/(q.totient:ℝ))*(1+Real.log q)*r := by ring
    _ ≤ ((L:ℝ)/(q.totient:ℝ))*(weightConstant*(1+Real.log A))*(1+Real.log A)*r := by
      apply mul_le_mul_of_nonneg_right _ hr
      apply mul_le_mul _ (by linarith) (by linarith)
        (mul_nonneg (by positivity) (mul_nonneg weightConstant_nonneg (by linarith)))
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

theorem boundedGcdRatio_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n : ℕ) (hn : 0 < n) (hLA : L≤A)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 0≤N) (J : ℕ→ℂ) (hJ : ∀ q∈S, ‖J q‖≤2*N) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * J q‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ)) := by
  dsimp only
  let K := weightConstant*(1+Real.log A)^2*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg weightConstant_nonneg (sq_nonneg _)) (Real.sqrt_nonneg _)
  have hcoef (q : ℕ) (hq : q∈S) :
      ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0)‖ ≤ K*((L:ℝ)/(q.totient:ℝ)) := by
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    obtain ⟨hq0,hqA⟩ := mem_Icc.mp hqR
    rw [dif_pos ⟨hq0,hqL⟩]
    letI : NeZero q := ⟨(show 0 < q from hq0).ne'⟩
    exact signedCoefficient_commonRatio hqL χ ψ n A hn hqA
  have hsum : ∑ q∈S,(L:ℝ)/(q.totient:ℝ) ≤ (weightConstant*(1+Real.log A))^2 :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (commonMultipleTotientWeight A L (NeZero.pos L) hLA)
  calc
    _ ≤ ∑ q∈S, ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0) *
        J q‖ := norm_sum_le _ _
    _ ≤ ∑ q∈S, (K*((L:ℝ)/(q.totient:ℝ)))*(2*N) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul (hcoef q hq) (hJ q hq)
        (norm_nonneg _) ((norm_nonneg _).trans (hcoef q hq))
    _ = K*(∑ q∈S,(L:ℝ)/(q.totient:ℝ))*(2*N) := by rw [← sum_mul,← mul_sum]
    _ ≤ K*((weightConstant*(1+Real.log A))^2)*(2*N) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hK) (by positivity)
    _ = _ := by dsimp [K];ring

theorem dyadicGcdRatio_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n : ℕ) (hn : 0 < n) (hLA : L≤A)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hρ1 : ρ.re≤1) (hσ : 3/4≤σ.re) (hσ1 : σ.re≤1)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ)) := by
  apply boundedGcdRatio_sum χ ψ A n hn hLA S hS N (by linarith)
  intro q hq
  exact dyadicPair_uniform (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hρ1 hσ hσ1

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.shiftedGauss_commonRatio
#print axioms InnerFloorGaussPacket.signedCoefficient_commonRatio
#print axioms InnerFloorGaussPacket.boundedGcdRatio_sum
#print axioms InnerFloorGaussPacket.dyadicGcdRatio_sum

section
open Set MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ContDiff BigOperators Interval
namespace InnerFloorZeroModel
noncomputable section
set_option maxHeartbeats 2000000 in
/-- Preserve both zero real parts in the exact taper pair bound, rather than
discarding their combined power saving by replacing the energy by O(N). -/
theorem dyadicPair_realParts (a b c d N : ℝ) (ρ σ : ℂ) (R n : ℝ)
    (ha : 0<a) (hb : a≤b+1) (hc : 0<c) (hd : c≤d+1)
    (hbN : b+1≤N) (hdN : d+1≤N) (hN : 1≤N) (hR : 0≤R)
    (hρ : 3/4≤ρ.re) (hσ : 3/4≤σ.re) :
    ‖dyadicPair a b c d ρ σ R n‖ ≤ 2*N^(ρ.re+σ.re-1) := by
  obtain ⟨hi₁,he₁⟩ := dyadicTransform_energy a b N ρ ha hb hbN (by linarith)
  obtain ⟨hi₂,he₂⟩ := dyadicTransform_energy c d N σ hc hd hdN (by linarith)
  have hN0 : 0<N := by linarith
  let X := N^(ρ.re-1/2)
  let Y := N^(σ.re-1/2)
  have hX : 0<X := Real.rpow_pos_of_pos hN0 _
  have hY : 0<Y := Real.rpow_pos_of_pos hN0 _
  have hXeq : N^(2*ρ.re-1)=X^2 := by
    dsimp [X]
    rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
    congr 1
    norm_num
    ring
  have hYeq : N^(2*σ.re-1)=Y^2 := by
    dsimp [Y]
    rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
    congr 1
    norm_num
    ring
  have hE₁ : (∫ v, ‖dyadicTransform a b ρ v‖^2) ≤ 2*X^2 := by
    apply he₁.trans
    rw [hXeq]
    apply (div_le_iff₀ (by linarith : 0<2*ρ.re-1)).2
    nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*(2*ρ.re-1) by linarith) (sq_nonneg X)]
  have hE₂ : (∫ v, ‖dyadicTransform c d σ v‖^2) ≤ 2*Y^2 := by
    apply he₂.trans
    rw [hYeq]
    apply (div_le_iff₀ (by linarith : 0<2*σ.re-1)).2
    nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*(2*σ.re-1) by linarith) (sq_nonneg Y)]
  let f (v : ℝ) := (‖dyadicTransform a b ρ v‖^2/X^2+‖dyadicTransform c d σ v‖^2/Y^2)/2
  have hf : Integrable f := ((hi₁.div_const (X^2)).add (hi₂.div_const (Y^2))).div_const 2
  have hF₁ : (∫ v, ‖dyadicTransform a b ρ v‖^2/X^2) ≤ 2 := by
    rw [integral_div]
    exact (div_le_iff₀ (pow_pos hX 2)).2 hE₁
  have hF₂ : (∫ v, ‖dyadicTransform c d σ v‖^2/Y^2) ≤ 2 := by
    rw [integral_div]
    exact (div_le_iff₀ (pow_pos hY 2)).2 hE₂
  have hF : (∫ v,f v) ≤ 2 := by
    dsimp [f]
    rw [integral_div,integral_add (hi₁.div_const _) (hi₂.div_const _)]
    linarith
  have hp (v : ℝ) :
      ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖≤(X*Y)*f v := by
    rw [norm_mul,norm_mul,norm_phase,mul_one]
    have h : ‖dyadicTransform a b ρ v‖*‖dyadicTransform c d σ v‖/(X*Y)≤f v := by
      dsimp [f]
      rw [show ‖dyadicTransform a b ρ v‖*‖dyadicTransform c d σ v‖/(X*Y)=
        (‖dyadicTransform a b ρ v‖/X)*(‖dyadicTransform c d σ v‖/Y) by
        field_simp]
      simp only [← div_pow]
      nlinarith [sq_nonneg (‖dyadicTransform a b ρ v‖/X-‖dyadicTransform c d σ v‖/Y)]
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hX hY)).1 h
  have hA : ∀ v,0≤(X*Y)*f v := by intro v;dsimp [f];positivity
  have hg : Integrable (fun v => (X*Y)*f v) := hf.const_mul _
  unfold dyadicPair
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  calc
    _ ≤ ∫ v in Ioc (-R) R, ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioc (-R) R,(X*Y)*f v :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hg.integrableOn (Filter.Eventually.of_forall hp)
    _ ≤ ∫ v,(X*Y)*f v := setIntegral_le_integral hg (Filter.Eventually.of_forall hA)
    _ ≤ 2*(X*Y) := by
      rw [integral_const_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hF (mul_pos hX hY).le
    _ = _ := by
      have hXY : X*Y=N^(ρ.re+σ.re-1) := by
        dsimp [X,Y]
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      rw [hXY]

end
end InnerFloorZeroModel
end
#print axioms InnerFloorZeroModel.dyadicPair_realParts

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem dyadicHighProduct_realParts_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hσ : 3/4≤σ.re)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N^(ρ.re+σ.re-1)*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  apply boundedHighProduct_sum χ ψ A n D hn hD hprod S hS (N^(ρ.re+σ.re-1)) (Real.rpow_nonneg (by linarith) _)
  intro q hq
  exact dyadicPair_realParts (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hσ

theorem dyadicGcdRatio_realParts_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n : ℕ) (hn : 0 < n) (hLA : L≤A)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hσ : 3/4≤σ.re)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N^(ρ.re+σ.re-1)*weightConstant^3*(1+Real.log A)^4*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ)) := by
  apply boundedGcdRatio_sum χ ψ A n hn hLA S hS (N^(ρ.re+σ.re-1)) (Real.rpow_nonneg (by linarith) _)
  intro q hq
  exact dyadicPair_realParts (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hσ

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.dyadicHighProduct_realParts_sum
#print axioms InnerFloorGaussPacket.dyadicGcdRatio_realParts_sum


open scoped BigOperators
namespace InnerFloorResearch
noncomputable section

/-- A signed packet family can be reduced to the exceptional intersection of
all failed gates, retaining exact residual signs rather than replacing those
terms by their absolute values. The budgets apply only to the packet model. -/
theorem signedResidualPartition {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (P Q R : ι → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred R] (N L C r m : ℝ)
    (hN : 0 ≤ N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ L^r)
    (hP : ∀ i ∈ s, P i → ‖z i‖ ≤ C*(N/L^(m+r)))
    (hQ : ∀ i ∈ s, Q i → ‖z i‖ ≤ C*(N/L^(m+r)))
    (hR : ∀ i ∈ s, R i → ‖z i‖ ≤ C*(N/L^(m+r))) :
    (∑ i ∈ s.filter (fun i => ¬P i ∧ ¬Q i ∧ ¬R i), (z i).re) - C*(N/L^m)
      ≤ ∑ i ∈ s, (z i).re := by
  classical
  let G := s.filter (fun i => P i ∨ Q i ∨ R i)
  let B := s.filter (fun i => ¬P i ∧ ¬Q i ∧ ¬R i)
  have hG : G ⊆ s := Finset.filter_subset _ _
  have hdisj : Disjoint G B := by
    apply Finset.disjoint_left.mpr
    intro i hiG hiB
    have hg := (Finset.mem_filter.mp hiG).2
    have hb := (Finset.mem_filter.mp hiB).2
    rcases hg with h | h | h
    · exact hb.1 h
    · exact hb.2.1 h
    · exact hb.2.2 h
  have hcover : G ∪ B = s := by
    ext i
    simp only [G,B,Finset.mem_union,Finset.mem_filter]
    tauto
  have hpos : 0 ≤ C*(N/L^(m+r)) := by positivity
  have hsum : ∑ i ∈ G, ‖z i‖ ≤ C*(N/L^m) := by
    calc
      ∑ i ∈ G, ‖z i‖ ≤ ∑ _i ∈ G, C*(N/L^(m+r)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hs := hG hi
        rcases (Finset.mem_filter.mp hi).2 with h | h | h
        · exact hP i hs h
        · exact hQ i hs h
        · exact hR i hs h
      _ = (G.card:ℝ)*(C*(N/L^(m+r))) := by simp
      _ ≤ L^r*(C*(N/L^(m+r))) := by
        apply mul_le_mul_of_nonneg_right _ hpos
        exact (show (G.card:ℝ) ≤ (s.card:ℝ) by exact_mod_cast Finset.card_le_card hG).trans hcard
      _ = C*(N/L^m) := by
        rw [Real.rpow_add hL]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hL m), ne_of_gt (Real.rpow_pos_of_pos hL r)]
  have hgood : -(C*(N/L^m)) ≤ ∑ i ∈ G, (z i).re := by
    have hn : -(∑ i ∈ G, ‖z i‖) ≤ ∑ i ∈ G, (z i).re := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have habs := Complex.abs_re_le_norm (z i)
      exact (neg_le_neg habs).trans (neg_abs_le _)
    linarith
  have hsplit : ∑ i ∈ s, (z i).re = (∑ i ∈ G, (z i).re) + (∑ i ∈ B, (z i).re) := by
    rw [← hcover, Finset.sum_union hdisj]
  change (∑ i ∈ B, (z i).re) - C*(N/L^m) ≤ _
  linarith

end
end InnerFloorResearch
#print axioms InnerFloorResearch.signedResidualPartition

open scoped BigOperators
namespace InnerFloorResearch
noncomputable section

/-- Exponential form of the quantitative zero-pair deficit, retaining the
    logarithmic loss of the sparse family. This is a conditional numerical
    estimate only, not a zero-free region. -/
theorem sparseDeficitTerm (N L b c k m : ℝ)
    (hN : 0 < N) (hL : 0 < L)
    (hgap : (k+m)*Real.log L ≤ (2-b-c)*Real.log N) :
    N^(b+c-1)*L^k ≤ N/L^m := by
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL m)).2
  rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos hL,
    Real.rpow_def_of_pos hL, ← Real.exp_add, ← Real.exp_add]
  calc
    _ ≤ Real.exp (Real.log N) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hgap]
    _ = N := Real.exp_log hN

/-- A log-power-sized packet family is small when each pair has the required
    real-part deficit, without multiplying by the total number of moduli. -/
theorem sparseDeficitSum {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (N L C r k m : ℝ)
    (b c : ι → ℝ) (hN : 0 < N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ L^r)
    (hw : ∀ i ∈ s, w i ≤ C * (N^(b i+c i-1)*L^k))
    (hgap : ∀ i ∈ s, (k+(m+r))*Real.log L ≤ (2-b i-c i)*Real.log N) :
    ∑ i ∈ s, w i ≤ C*(N/L^m) := by
  have hden : 0 < L^(m+r) := Real.rpow_pos_of_pos hL _
  have hq : 0 ≤ C*(N/L^(m+r)) := mul_nonneg hC (div_nonneg hN.le hden.le)
  calc
    ∑ i ∈ s, w i ≤ ∑ _i ∈ s, C*(N/L^(m+r)) :=
      Finset.sum_le_sum fun i hi => (hw i hi).trans
        (mul_le_mul_of_nonneg_left (sparseDeficitTerm N L (b i) (c i) k (m+r) hN hL (hgap i hi)) hC)
    _ = (s.card : ℝ)*(C*(N/L^(m+r))) := by simp
    _ ≤ L^r*(C*(N/L^(m+r))) := mul_le_mul_of_nonneg_right hcard hq
    _ = C*(N/L^m) := by
      rw [Real.rpow_add hL]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hL m), ne_of_gt (Real.rpow_pos_of_pos hL r)]

end
end InnerFloorResearch
#print axioms InnerFloorResearch.sparseDeficitTerm
#print axioms InnerFloorResearch.sparseDeficitSum

namespace InnerFloorResearch
noncomputable section
open scoped BigOperators

/-- Convert a saving factor to an inverse logarithmic budget. -/
theorem packetSavingBudget (N L C b c k m r g : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C) (hg : 0 ≤ g)
    (hb : b+c ≤ 2) (hgate : L^(k+(m+r))*g ≤ 1) :
    C*(N^(b+c-1)*L^k)*g ≤ C*(N/L^(m+r)) := by
  have hn : 0 < N := by linarith
  have hpow : N^(b+c-1) ≤ N := by
    conv_rhs => rw [← Real.rpow_one N]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hLr : 0 < L^(m+r) := Real.rpow_pos_of_pos hL _
  have hsmall : L^k*g ≤ 1/L^(m+r) := by
    apply (le_div_iff₀ hLr).2
    rw [Real.rpow_add hL] at hgate
    linarith only [show L^k*g*L^(m+r) = L^k*L^(m+r)*g by ring,hgate]
  calc
    _ = C*(N^(b+c-1)*(L^k*g)) := by ring
    _ ≤ C*(N*(1/L^(m+r))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul hpow hsmall (by positivity) hn.le
    _ = _ := by ring

/-- All three quantitative mechanisms simultaneously.  The unsolved term is
exactly the intersection of their failure regions, not a signed estimate
for an unrelated union of arcs. -/
theorem quantitativeResidualPartition {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (b c u v : ι → ℝ) (N L C k r m : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card:ℝ) ≤ L^r)
    (hb : ∀ i ∈ s, b i+c i ≤ 2)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (h0 : ∀ i ∈ s, ‖z i‖ ≤ C*(N^(b i+c i-1)*L^k))
    (h1 : ∀ i ∈ s, ‖z i‖ ≤ C*(N^(b i+c i-1)*L^k)*u i)
    (h2 : ∀ i ∈ s, ‖z i‖ ≤ C*(N^(b i+c i-1)*L^k)*v i) :
    (∑ i ∈ s.filter (fun i =>
      (2-b i-c i)*Real.log N < (k+(m+r))*Real.log L ∧
      1 < L^(k+(m+r))*u i ∧ 1 < L^(k+(m+r))*v i), (z i).re)
      - C*(N/L^m) ≤ ∑ i ∈ s, (z i).re := by
  classical
  let P (i : ι) := (k+(m+r))*Real.log L ≤ (2-b i-c i)*Real.log N
  let Q (i : ι) := L^(k+(m+r))*u i ≤ 1
  let R (i : ι) := L^(k+(m+r))*v i ≤ 1
  have hn : 0 < N := by linarith
  have hP : ∀ i ∈ s, P i → ‖z i‖ ≤ C*(N/L^(m+r)) := by
    intro i hi hp
    exact (h0 i hi).trans (mul_le_mul_of_nonneg_left
      (sparseDeficitTerm N L (b i) (c i) k (m+r) hn hL hp) hC)
  have hQ : ∀ i ∈ s, Q i → ‖z i‖ ≤ C*(N/L^(m+r)) := by
    intro i hi hq
    exact (h1 i hi).trans (packetSavingBudget N L C (b i) (c i) k m r (u i) hN hL hC (hu i hi) (hb i hi) hq)
  have hR : ∀ i ∈ s, R i → ‖z i‖ ≤ C*(N/L^(m+r)) := by
    intro i hi hr
    exact (h2 i hi).trans (packetSavingBudget N L C (b i) (c i) k m r (v i) hN hL hC (hv i hi) (hb i hi) hr)
  simpa only [P,Q,R,not_le] using signedResidualPartition s z P Q R N L C r m
    hn.le hL hC hcard hP hQ hR

end
end InnerFloorResearch
#print axioms InnerFloorResearch.packetSavingBudget
#print axioms InnerFloorResearch.quantitativeResidualPartition

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

/-- Data for one primitive-zero pair, lifted to a common level. The windows
may vary with the rational denominator; the arc mask is kept as a subset. -/
structure DyadicPacket where
  level : ℕ
  level_pos : 0 < level
  χ : DirichletCharacter ℂ level
  ψ : DirichletCharacter ℂ level
  ρ : ℂ
  σ : ℂ
  S : Finset ℕ
  a : ℕ → ℝ
  b : ℕ → ℝ
  c : ℕ → ℝ
  d : ℕ → ℝ
  R : ℕ → ℝ

def DyadicPacket.value (p : DyadicPacket) (n : ℕ) : ℂ :=
  ∑ q∈p.S, (if h : 0 < q ∧ p.level ∣ q then
    letI : NeZero q := ⟨h.1.ne'⟩
    signedCoefficient (DirichletCharacter.changeLevel h.2 p.χ)
      (DirichletCharacter.changeLevel h.2 p.ψ) n else 0) *
    dyadicPair (p.a q) (p.b q) (p.c q) (p.d q) p.ρ p.σ (p.R q) n

def DyadicPacket.productSaving (p : DyadicPacket) : ℝ :=
  letI : NeZero p.level := ⟨p.level_pos.ne'⟩
  1 / Real.sqrt ((p.χ*p.ψ).conductor:ℝ)

def DyadicPacket.gcdSaving (p : DyadicPacket) (n : ℕ) : ℝ :=
  Real.sqrt ((Nat.gcd n p.level:ℝ)/(p.level:ℝ))

structure DyadicPacket.Admissible (p : DyadicPacket) (A : ℕ) (N : ℝ) : Prop where
  hLA : p.level ≤ A
  hS : p.S ⊆ (Icc 1 A).filter (fun q => p.level∣q)
  hρ : 3/4≤p.ρ.re
  hσ : 3/4≤p.σ.re
  hsum : p.ρ.re+p.σ.re≤2
  ha : ∀ q∈p.S, 0<p.a q
  hb : ∀ q∈p.S, p.a q≤p.b q+1
  hc : ∀ q∈p.S, 0<p.c q
  hd : ∀ q∈p.S, p.c q≤p.d q+1
  hbN : ∀ q∈p.S, p.b q+1≤N
  hdN : ∀ q∈p.S, p.d q+1≤N
  hR : ∀ q∈p.S, 0≤p.R q

/-- The same actual Gauss-normalized packet has all three bounds, with no
zero-free hypothesis, and no assertion about the prime spectral expansion. -/
theorem DyadicPacket.threeBounds (p : DyadicPacket) (A n : ℕ) (N : ℝ)
    (hn : 0<n) (hN : 1≤N) (hp : p.Admissible A N) :
    let B := (2*weightConstant^3)*(N^(p.ρ.re+p.σ.re-1)*(1+Real.log A)^(4:ℝ))
    ‖p.value n‖ ≤ B ∧ ‖p.value n‖ ≤ B*p.productSaving ∧
      ‖p.value n‖ ≤ B*p.gcdSaving n := by
  letI : NeZero p.level := ⟨p.level_pos.ne'⟩
  let D := (p.χ*p.ψ).conductor
  have hD : 0<D := Nat.pos_of_dvd_of_pos (p.χ*p.ψ).conductor_dvd_level p.level_pos
  have h0 := dyadicHighProduct_realParts_sum p.χ p.ψ A n 1 hn (by omega)
    (show 1≤D by omega) p.S hp.hS N hN p.ρ p.σ hp.hρ hp.hσ p.a p.b p.c p.d p.R
    hp.ha hp.hb hp.hc hp.hd hp.hbN hp.hdN hp.hR
  have h1 := dyadicHighProduct_realParts_sum p.χ p.ψ A n D hn hD le_rfl p.S hp.hS
    N hN p.ρ p.σ hp.hρ hp.hσ p.a p.b p.c p.d p.R
    hp.ha hp.hb hp.hc hp.hd hp.hbN hp.hdN hp.hR
  have h2 := dyadicGcdRatio_realParts_sum p.χ p.ψ A n hn hp.hLA p.S hp.hS
    N hN p.ρ p.σ hp.hρ hp.hσ p.a p.b p.c p.d p.R
    hp.ha hp.hb hp.hc hp.hd hp.hbN hp.hdN hp.hR
  dsimp only at h0 h1 h2 ⊢
  rw [show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast]
  constructor
  · change ‖p.value n‖ ≤ _
    apply (show ‖p.value n‖ ≤ _ from h0).trans_eq
    norm_num
    ring
  constructor
  · change ‖p.value n‖ ≤ _
    apply (show ‖p.value n‖ ≤ _ from h1).trans_eq
    unfold DyadicPacket.productSaving
    dsimp [D]
    ring
  · change ‖p.value n‖ ≤ _
    apply (show ‖p.value n‖ ≤ _ from h2).trans_eq
    unfold DyadicPacket.gcdSaving
    ring

/-- Exact three-gate residual bound for any sparse collection of actual
Gauss-normalized tapered zero pairs. Only the residual intersection needs a
signed lower bound, provided the spectral expansion and sparsity are proved. -/
theorem actualPacketResidual {ι : Type*} (s : Finset ι) (p : ι→DyadicPacket)
    (A n : ℕ) (N r m : ℝ) (hA : 1≤A) (hn : 0<n) (hN : 1≤N)
    (hp : ∀ i∈s, (p i).Admissible A N)
    (hcard : (s.card:ℝ) ≤ (1+Real.log A)^r) :
    let L := 1+Real.log A
    (∑ i∈s.filter (fun i =>
      (2-(p i).ρ.re-(p i).σ.re)*Real.log N < (4+(m+r))*Real.log L ∧
      1 < L^(4+(m+r))*(p i).productSaving ∧
      1 < L^(4+(m+r))*(p i).gcdSaving n), ((p i).value n).re)
      -(2*weightConstant^3)*(N/L^m) ≤ ∑ i∈s, ((p i).value n).re := by
  dsimp only
  have hlog : 0 < 1+Real.log A := by
    linarith [Real.log_nonneg (show (1:ℝ)≤A by exact_mod_cast hA)]
  apply quantitativeResidualPartition s (fun i => (p i).value n)
    (fun i => (p i).ρ.re) (fun i => (p i).σ.re)
    (fun i => (p i).productSaving) (fun i => (p i).gcdSaving n)
    N (1+Real.log A) (2*weightConstant^3) 4 r m hN hlog
    (mul_nonneg (by norm_num) (pow_nonneg weightConstant_nonneg 3)) hcard
  · intro i hi; exact (hp i hi).hsum
  · intro i hi; unfold DyadicPacket.productSaving; positivity
  · intro i hi; unfold DyadicPacket.gcdSaving; positivity
  · intro i hi; exact ((p i).threeBounds A n N hn hN (hp i hi)).1
  · intro i hi; exact ((p i).threeBounds A n N hn hN (hp i hi)).2.1
  · intro i hi; exact ((p i).threeBounds A n N hn hN (hp i hi)).2.2

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.DyadicPacket.threeBounds
#print axioms InnerFloorGaussPacket.actualPacketResidual


open Finset
open scoped Classical
namespace InnerFloorDensityPair
noncomputable section

/-- The density budget at a prescribed logarithmic cutoff.  No density
    theorem is asserted here: the accepted density bound supplies hden. -/
theorem densityBudget (X Q T δ c C M : ℝ)
    (hX : Real.exp 1 ≤ X) (hQ : 1 ≤ Q) (hT : 2 ≤ T)
    (hQX : Q ≤ X) (hlog : Real.log (Q*T) ≤ 2*Real.log X)
    (hδ : 0 ≤ δ) (hc : δ*Real.log X ≤ c*Real.log (Real.log X))
    (hC : 0 ≤ C)
    (hden : M ≤ C*(Q^2*T)^(3*δ/(1+δ))*Real.log (Q*T)^13) :
    M ≤ C*2^13*(Real.log X)^(9*c+13) := by
  have hX1 : 1 < X := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hXp : 0 < X := by linarith
  have hLp : 0 < Real.log X := Real.log_pos hX1
  have hQp : 0 < Q := by linarith
  have hTp : 0 < T := by linarith
  have hbase : 1 ≤ Q^2*T := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ) (by linarith)
  have hQT : Q*T ≤ X^2 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hlog
  have hbaseX : Q^2*T ≤ X^3 := by
    calc
      _ = Q*(Q*T) := by ring
      _ ≤ X*(X^2) := mul_le_mul hQX hQT (by positivity) hXp.le
      _ = _ := by ring
  have hexp : 3*δ/(1+δ) ≤ 3*δ := div_le_self (by positivity) (by linarith)
  have hpower : (Q^2*T)^(3*δ/(1+δ)) ≤ (Real.log X)^(9*c) := by
    calc
      _ ≤ (Q^2*T)^(3*δ) := Real.rpow_le_rpow_of_exponent_le hbase hexp
      _ ≤ (X^3)^(3*δ) := Real.rpow_le_rpow (by positivity) hbaseX (by positivity)
      _ = X^(9*δ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]; congr 1; norm_num; ring
      _ ≤ (Real.log X)^(9*c) := by
        rw [Real.rpow_def_of_pos hXp, Real.rpow_def_of_pos hLp]
        apply Real.exp_le_exp.mpr
        linarith only [hc]
  have hlog0 : 0 ≤ Real.log (Q*T) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQ (by linarith))
  have hlogpow : Real.log (Q*T)^13 ≤ (2*Real.log X)^13 := pow_le_pow_left₀ hlog0 hlog 13
  calc
    M ≤ _ := hden
    _ ≤ C*(Real.log X)^(9*c)*(2*Real.log X)^13 := by gcongr
    _ = _ := by
      have h13 : (Real.log X)^(13:ℝ) = (Real.log X)^(13:ℕ) := by
        simpa only [Nat.cast_ofNat] using (Real.rpow_natCast (Real.log X) 13)
      rw [mul_pow, Real.rpow_add hLp, h13]
      ring

/-- Ordered zero-pair occurrences, not distinct complex values: the product
    preserves multiplicity because the occurrence identifiers are retained. -/
theorem pairCard {ι : Type*} (s : Finset ι) (L K a : ℝ)
    (hL : 0<L) (hK : 0≤K) (hc : (s.card:ℝ) ≤ K*L^a) :
    ((s ×ˢ s).card:ℝ) ≤ K^2*L^(2*a) := by
  rw [Finset.card_product, Nat.cast_mul]
  calc
    _ ≤ (K*L^a)*(K*L^a) := mul_le_mul hc hc (by positivity) (by positivity)
    _ = _ := by
      rw [show 2*a=a+a by ring,Real.rpow_add hL]
      ring

/-- Absorb the fixed density constant into an extra log exponent eventually.
    This avoids assuming a cardinality bound with leading constant one. -/
theorem absorbPairConstant {ι : Type*} (s : Finset ι) (L K a : ℝ)
    (hL : 1≤L) (hK : 0≤K) (hK2 : K^2≤L)
    (hc : (s.card:ℝ)≤K*L^a) : ((s ×ˢ s).card:ℝ)≤L^(2*a+1) := by
  have hLp : 0<L := by linarith
  calc
    _ ≤ K^2*L^(2*a) := pairCard s L K a hLp hK hc
    _ ≤ L*L^(2*a) := mul_le_mul_of_nonneg_right hK2 (by positivity)
    _ = _ := by rw [Real.rpow_add hLp,Real.rpow_one];ring

end
end InnerFloorDensityPair
#print axioms InnerFloorDensityPair.densityBudget
#print axioms InnerFloorDensityPair.pairCard
#print axioms InnerFloorDensityPair.absorbPairConstant


open Finset OAI.Ostmann
open scoped Classical
namespace InnerFloorOccurrence
noncomputable section

abbrev Occurrence := Σ _χ : PrimitiveComplexCharacter, ℕ

def nearOneIndices (δ T : ℝ) (χ : PrimitiveComplexCharacter) : Finset ℕ :=
  ((V1 χ).V14 T).filter (fun i => 1-δ < ((V1 χ).zeros i).re)

def occurrences (F : Finset PrimitiveComplexCharacter) (δ T : ℝ) : Finset Occurrence :=
  F.sigma (nearOneIndices δ T)

def pairs (F : Finset PrimitiveComplexCharacter) (δ T : ℝ) (A : ℕ) :
    Finset (Occurrence × Occurrence) :=
  ((occurrences F δ T) ×ˢ (occurrences F δ T)).filter
    (fun ij => Nat.lcm ij.1.1.modulus ij.2.1.modulus ≤ A)

def zero (i : Occurrence) : ℂ := (V1 i.1).zeros i.2

theorem occurrence_in_strip (i : Occurrence) : 0 < (zero i).re ∧ (zero i).re < 1 :=
  (V1 i.1).in_strip i.2

theorem occurrence_actual_zero (i : Occurrence) : i.1.L (zero i) = 0 :=
  (V1 i.1).actual_zero i.2

theorem occurrenceNearOne {F : Finset PrimitiveComplexCharacter} {δ T : ℝ}
    {i : Occurrence} (hi : i∈occurrences F δ T) :
    i.1∈F ∧ |(zero i).im|≤T ∧ 1-δ < (zero i).re := by
  have h := Finset.mem_sigma.mp hi
  have h' := Finset.mem_filter.mp h.2
  exact ⟨h.1, ((V1 i.1).V2r T i.2).mp h'.1, h'.2⟩

/-- Every actual occurrence is counted by the accepted density theorem V1f0;
    the index, rather than its complex value, preserves multiplicities. -/
theorem occurrenceBudget : ∃ K : ℝ, 0<K ∧
    ∀ (F : Finset PrimitiveComplexCharacter) (Q : ℕ) (X T δ c : ℝ),
      1≤Q → Real.exp 1≤X → 2≤T → (Q:ℝ)≤X →
      Real.log ((Q:ℝ)*T)≤2*Real.log X → 0≤δ → δ≤1/2 →
      δ*Real.log X≤c*Real.log (Real.log X) →
      (∀ χ∈F, χ.modulus≤Q) →
      ((occurrences F δ T).card:ℝ)≤K*(Real.log X)^(9*c+13) := by
  obtain ⟨C,hC,hden⟩ := V1f0
  refine ⟨C*2^13,by positivity,?_⟩
  intro F Q X T δ c hQ hX hT hQX hlog hδ hδ' hc hF
  have hcard : ((occurrences F δ T).card:ℝ) ≤
      ∑ χ∈F, ((V1 χ).count (1-δ) T:ℝ) := by
    rw [occurrences,Finset.card_sigma,Nat.cast_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    apply Nat.cast_le.mpr
    unfold nearOneIndices ComplexZeroEnumeration.count
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2.le⟩
  have hd := hden Q hQ T (1-δ) hT (by linarith) (by linarith) F hF
  rw [show (1:ℝ)-(1-δ)=δ by ring,show (2:ℝ)-(1-δ)=1+δ by ring] at hd
  exact InnerFloorDensityPair.densityBudget X Q T δ c C ((occurrences F δ T).card:ℝ)
    hX (by exact_mod_cast hQ) hT hQX hlog hδ hc hC.le (hcard.trans hd)

/-- Filter out pairs that cannot have any common denominator in the range.
    Pair indexing still distinguishes repeated occurrences. -/
theorem pairBudget {F : Finset PrimitiveComplexCharacter} {δ T L K a : ℝ}
    (A : ℕ) (hL : 1≤L) (hK : 0≤K) (hK2 : K^2≤L)
    (hcard : ((occurrences F δ T).card:ℝ)≤K*L^a) :
    ((pairs F δ T A).card:ℝ)≤L^(2*a+1) := by
  have hs : pairs F δ T A ⊆ (occurrences F δ T) ×ˢ (occurrences F δ T) :=
    Finset.filter_subset _ _
  exact (show ((pairs F δ T A).card:ℝ)≤(((occurrences F δ T) ×ˢ (occurrences F δ T)).card:ℝ) by
    exact_mod_cast Finset.card_le_card hs).trans
    (InnerFloorDensityPair.absorbPairConstant (occurrences F δ T) L K a hL hK hK2 hcard)

/-- No low-product/conductor gate is used in the counting stage. -/
theorem pairNearOne {F : Finset PrimitiveComplexCharacter} {δ T : ℝ} {A : ℕ}
    {ij : Occurrence × Occurrence} (hi : ij∈pairs F δ T A) (hδ : δ≤1/4) :
    3/4≤(zero ij.1).re ∧ 3/4≤(zero ij.2).re ∧
    (zero ij.1).re+(zero ij.2).re≤2 ∧
    Nat.lcm ij.1.1.modulus ij.2.1.modulus≤A := by
  have h := Finset.mem_filter.mp hi
  have hp := Finset.mem_product.mp h.1
  have h₁ := (occurrenceNearOne hp.1).2.2
  have h₂ := (occurrenceNearOne hp.2).2.2
  exact ⟨by linarith,by linarith,by linarith [(occurrence_in_strip ij.1).2,(occurrence_in_strip ij.2).2],h.2⟩

end
end InnerFloorOccurrence
#print axioms InnerFloorOccurrence.occurrenceBudget
#print axioms InnerFloorOccurrence.pairBudget
#print axioms InnerFloorOccurrence.pairNearOne
namespace InnerFloorOccurrence
open Finset OAI.Ostmann InnerFloorGaussPacket InnerFloorLinearTotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

abbrev Pair := Occurrence × Occurrence

def pairLevel (ij : Pair) : ℕ := Nat.lcm ij.1.1.modulus ij.2.1.modulus

theorem pairLevel_pos (ij : Pair) : 0 < pairLevel ij :=
  Nat.lcm_pos ij.1.1.positive ij.2.1.positive

/-- The common denominator is the lcm, not an arbitrary input level. -/
def packet (ij : Pair) (S : Finset ℕ) (a b c d R : ℕ→ℝ) : DyadicPacket where
  level := pairLevel ij
  level_pos := pairLevel_pos ij
  χ := DirichletCharacter.changeLevel (Nat.dvd_lcm_left _ _) ij.1.1.character
  ψ := DirichletCharacter.changeLevel (Nat.dvd_lcm_right _ _) ij.2.1.character
  ρ := zero ij.1
  σ := zero ij.2
  S := S.filter (fun q => pairLevel ij ∣ q)
  a := a
  b := b
  c := c
  d := d
  R := R

/-- Two successive lifts are the direct lift of the original characters. -/
theorem packet_lift_left (ij : Pair) (S : Finset ℕ) (a b c d R : ℕ→ℝ)
    {q : ℕ} (h : pairLevel ij ∣ q) :
    DirichletCharacter.changeLevel h (packet ij S a b c d R).χ =
      DirichletCharacter.changeLevel ((Nat.dvd_lcm_left ij.1.1.modulus ij.2.1.modulus).trans h) ij.1.1.character := by
  exact (DirichletCharacter.changeLevel_trans ij.1.1.character _ h).symm

theorem packet_lift_right (ij : Pair) (S : Finset ℕ) (a b c d R : ℕ→ℝ)
    {q : ℕ} (h : pairLevel ij ∣ q) :
    DirichletCharacter.changeLevel h (packet ij S a b c d R).ψ =
      DirichletCharacter.changeLevel ((Nat.dvd_lcm_right ij.1.1.modulus ij.2.1.modulus).trans h) ij.2.1.character := by
  exact (DirichletCharacter.changeLevel_trans ij.2.1.character _ h).symm

/-- Common log scale: A can be much smaller than N. We only use
    log A ≤ log N, never identify these two scales. -/
theorem packetThreeBoundsAtScale (p : DyadicPacket) (A n : ℕ) (N : ℝ)
    (hA : 1≤A) (hAN : (A:ℝ)≤N) (hn : 0<n) (hN : 1≤N)
    (hp : p.Admissible A N) :
    let B := (2*weightConstant^3)*(N^(p.ρ.re+p.σ.re-1)*(1+Real.log N)^(4:ℝ))
    ‖p.value n‖ ≤ B ∧ ‖p.value n‖ ≤ B*p.productSaving ∧
      ‖p.value n‖ ≤ B*p.gcdSaving n := by
  have h := p.threeBounds A n N hn hN hp
  dsimp only at h ⊢
  have hA1 : (1:ℝ)≤A := by exact_mod_cast hA
  have hlog : 0≤1+Real.log A := by linarith [Real.log_nonneg hA1]
  have hb : 1+Real.log A≤1+Real.log N := by
    linarith [Real.log_le_log (show (0:ℝ)<A by linarith) hAN]
  have hp4 : (1+Real.log A)^(4:ℝ)≤(1+Real.log N)^(4:ℝ) :=
    Real.rpow_le_rpow hlog hb (by norm_num)
  have hC : 0≤2*weightConstant^3 := mul_nonneg (by norm_num) (pow_nonneg weightConstant_nonneg 3)
  have hb' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp4
    (Real.rpow_nonneg (by linarith : 0≤N) (p.ρ.re+p.σ.re-1))) hC
  exact ⟨h.1.trans hb',h.2.1.trans (mul_le_mul_of_nonneg_right hb' (by unfold DyadicPacket.productSaving; positivity)),
    h.2.2.trans (mul_le_mul_of_nonneg_right hb' (by unfold DyadicPacket.gcdSaving; positivity))⟩

/-- End-to-end density to signed residual, with original zero occurrences,
    common-level lifts and a single explicit log scale.  The windows and
    finite primitive-character family are inputs from the spectral expansion. -/
theorem occurrenceResidual : ∃ K : ℝ, 0<K ∧
    ∀ (F : Finset PrimitiveComplexCharacter) (A n : ℕ) (N T δ c₀ m : ℝ),
      1≤A → 0<n → Real.exp 1≤N → 2≤T → (A:ℝ)≤N →
      Real.log ((A:ℝ)*T)≤2*Real.log N → 0≤δ → δ≤1/4 →
      δ*Real.log N≤c₀*Real.log (Real.log N) → 0≤c₀ → K^2≤1+Real.log N →
      (∀ χ∈F, χ.modulus≤A) →
      ∀ (S : Finset ℕ) (a b c d R : Pair→ℕ→ℝ),
      S ⊆ Icc 1 A →
      (∀ ij∈pairs F δ T A, ∀ q∈S, 0<a ij q ∧ a ij q≤b ij q+1 ∧
        0<c ij q ∧ c ij q≤d ij q+1 ∧ b ij q+1≤N ∧ d ij q+1≤N ∧ 0≤R ij q) →
      let L := 1+Real.log N
      let r := 2*(9*c₀+13)+1
      let s := pairs F δ T A
      let p := fun ij => packet ij S (a ij) (b ij) (c ij) (d ij) (R ij)
      (∑ ij∈s.filter (fun ij =>
        (2-(zero ij.1).re-(zero ij.2).re)*Real.log N < (4+(m+r))*Real.log L ∧
        1 < L^(4+(m+r))*(p ij).productSaving ∧
        1 < L^(4+(m+r))*(p ij).gcdSaving n), ((p ij).value n).re)
        -(2*weightConstant^3)*(N/L^m) ≤ ∑ ij∈s, ((p ij).value n).re := by
  obtain ⟨K,hK,hbudget⟩ := occurrenceBudget
  refine ⟨K,hK,?_⟩
  intro F A n N T δ c₀ m hA hn hN hT hAN hlog hδ hδ' hcut hc₀ hK2 hF S a b c d R hS hw
  dsimp only
  let L := 1+Real.log N
  let r := 2*(9*c₀+13)+1
  let s := pairs F δ T A
  let p := fun ij => packet ij S (a ij) (b ij) (c ij) (d ij) (R ij)
  have hN1 : 1≤N := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hlogN : 1≤Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hN
  have hL : 1≤L := by dsimp [L]; linarith
  have hLp : 0<L := by linarith
  have hc : ((occurrences F δ T).card:ℝ)≤K*L^(9*c₀+13) := by
    apply (hbudget F A N T δ c₀ hA hN hT hAN hlog hδ (by linarith) hcut hF).trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.rpow_le_rpow (by linarith : 0≤Real.log N) (by dsimp [L]; linarith)
    linarith
  have hcard : (s.card:ℝ)≤L^r := pairBudget A hL hK.le hK2 hc
  have hadm : ∀ ij∈s, (p ij).Admissible A N := by
    intro ij hij
    have hnz := pairNearOne hij hδ'
    constructor
    · exact hnz.2.2.2
    · intro q hq
      have h := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hS h.1,h.2⟩
    · exact hnz.1
    · exact hnz.2.1
    · exact hnz.2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.2.2.2.1
    · intro q hq; exact (hw ij hij q (Finset.mem_filter.mp hq).1).2.2.2.2.2.2
  apply InnerFloorResearch.quantitativeResidualPartition s (fun ij => (p ij).value n)
    (fun ij => (zero ij.1).re) (fun ij => (zero ij.2).re)
    (fun ij => (p ij).productSaving) (fun ij => (p ij).gcdSaving n)
    N L (2*weightConstant^3) 4 r m hN1 hLp
    (mul_nonneg (by norm_num) (pow_nonneg weightConstant_nonneg 3)) hcard
  · intro ij hi; exact (hadm ij hi).hsum
  · intro ij hi; unfold DyadicPacket.productSaving; positivity
  · intro ij hi; unfold DyadicPacket.gcdSaving; positivity
  · intro ij hi; exact (packetThreeBoundsAtScale (p ij) A n N hA hAN hn hN1 (hadm ij hi)).1
  · intro ij hi; exact (packetThreeBoundsAtScale (p ij) A n N hA hAN hn hN1 (hadm ij hi)).2.1
  · intro ij hi; exact (packetThreeBoundsAtScale (p ij) A n N hA hAN hn hN1 (hadm ij hi)).2.2

end
end InnerFloorOccurrence
#print axioms InnerFloorOccurrence.packet_lift_left
#print axioms InnerFloorOccurrence.packet_lift_right
#print axioms InnerFloorOccurrence.packetThreeBoundsAtScale
#print axioms InnerFloorOccurrence.occurrenceResidual

namespace InnerFloorOccurrence
open Finset OAI.Ostmann InnerFloorGaussPacket InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

/-- Denominator-first term using the original primitive characters, not
    independently chosen characters at the common level. -/
def denominatorTerm (ij : Pair) (q n : ℕ) (a b c d R : ℕ→ℝ) : ℂ :=
  (if h : 0<q ∧ pairLevel ij∣q then
    letI : NeZero q := ⟨h.1.ne'⟩
    signedCoefficient
      (DirichletCharacter.changeLevel ((Nat.dvd_lcm_left ij.1.1.modulus ij.2.1.modulus).trans h.2) ij.1.1.character)
      (DirichletCharacter.changeLevel ((Nat.dvd_lcm_right ij.1.1.modulus ij.2.1.modulus).trans h.2) ij.2.1.character) n
  else 0) * dyadicPair (a q) (b q) (c q) (d q) (zero ij.1) (zero ij.2) (R q) n

/-- Pair packet equals sum of original-character terms over all denominators.
    Terms at incompatible denominators are exactly zero. -/
theorem packet_value_eq (ij : Pair) (S : Finset ℕ) (n : ℕ) (a b c d R : ℕ→ℝ) :
    (packet ij S a b c d R).value n = ∑ q∈S, denominatorTerm ij q n a b c d R := by
  unfold DyadicPacket.value
  change (∑ q∈S.filter (fun q => pairLevel ij∣q),
    (if h : 0<q ∧ pairLevel ij∣q then
      letI : NeZero q := ⟨h.1.ne'⟩
      signedCoefficient
        (DirichletCharacter.changeLevel h.2
          (DirichletCharacter.changeLevel (Nat.dvd_lcm_left ij.1.1.modulus ij.2.1.modulus) ij.1.1.character))
        (DirichletCharacter.changeLevel h.2
          (DirichletCharacter.changeLevel (Nat.dvd_lcm_right ij.1.1.modulus ij.2.1.modulus) ij.2.1.character)) n
    else 0) * dyadicPair (a q) (b q) (c q) (d q) (zero ij.1) (zero ij.2) (R q) n) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : pairLevel ij∣q
  · rw [if_pos h]
    unfold denominatorTerm
    by_cases hq0 : 0<q
    · have hh : 0<q ∧ pairLevel ij∣q := ⟨hq0,h⟩
      simp only [dif_pos hh]
      letI : NeZero q := ⟨hq0.ne'⟩
      exact congrArg₂ (fun x y : DirichletCharacter ℂ q =>
        signedCoefficient x y n * dyadicPair (a q) (b q) (c q) (d q) (zero ij.1) (zero ij.2) (R q) n)
        (packet_lift_left ij S a b c d R h) (packet_lift_right ij S a b c d R h)
    · have hh : ¬(0<q ∧ pairLevel ij∣q) := fun ht => hq0 ht.1
      simp only [dif_neg hh]
  · rw [if_neg h]
    unfold denominatorTerm
    have hh : ¬(0<q ∧ pairLevel ij∣q) := fun ht => h ht.2
    rw [dif_neg hh,zero_mul]

/-- Exact interchange of denominator-first and pair-first sums, including
    elimination of lcm>A pairs, with no loss or cancellation assumed. -/
theorem reindexDenominatorSum (F : Finset PrimitiveComplexCharacter)
    (δ T : ℝ) (A n : ℕ) (S : Finset ℕ)
    (a b c d R : Pair→ℕ→ℝ) (hS : S⊆Icc 1 A) :
    (∑ q∈S, ∑ ij∈(occurrences F δ T) ×ˢ (occurrences F δ T),
      denominatorTerm ij q n (a ij) (b ij) (c ij) (d ij) (R ij)) =
    ∑ ij∈pairs F δ T A, (packet ij S (a ij) (b ij) (c ij) (d ij) (R ij)).value n := by
  rw [Finset.sum_comm]
  unfold pairs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ij hij
  by_cases h : Nat.lcm ij.1.1.modulus ij.2.1.modulus≤A
  · rw [if_pos h]
    exact (packet_value_eq ij S n (a ij) (b ij) (c ij) (d ij) (R ij)).symm
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro q hq
    unfold denominatorTerm
    have hq' := Finset.mem_Icc.mp (hS hq)
    rw [dif_neg (fun hh => h ((Nat.le_of_dvd (by omega : 0<q) hh.2).trans hq'.2)),zero_mul]

end
end InnerFloorOccurrence
#print axioms InnerFloorOccurrence.packet_value_eq
#print axioms InnerFloorOccurrence.reindexDenominatorSum

namespace InnerFloorOccurrence
open Finset OAI.Ostmann InnerFloorGaussPacket InnerFloorLinearTotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

/-- Final aggregation interface, in the denominator-first order used by
    the prime spectral expansion. The only untreated part is the signed
    triple-gate intersection of genuine near-one zero occurrences. -/
theorem denominatorResidualFloor : ∃ K : ℝ, 0<K ∧
    ∀ (F : Finset PrimitiveComplexCharacter) (A n : ℕ) (N T δ c₀ m : ℝ),
      1≤A → 0<n → Real.exp 1≤N → 2≤T → (A:ℝ)≤N →
      Real.log ((A:ℝ)*T)≤2*Real.log N → 0≤δ → δ≤1/4 →
      δ*Real.log N≤c₀*Real.log (Real.log N) → 0≤c₀ → K^2≤1+Real.log N →
      (∀ χ∈F, χ.modulus≤A) →
      ∀ (S : Finset ℕ) (a b c d R : Pair→ℕ→ℝ),
      S ⊆ Icc 1 A →
      (∀ ij∈pairs F δ T A, ∀ q∈S, 0<a ij q ∧ a ij q≤b ij q+1 ∧
        0<c ij q ∧ c ij q≤d ij q+1 ∧ b ij q+1≤N ∧ d ij q+1≤N ∧ 0≤R ij q) →
      let L := 1+Real.log N
      let r := 2*(9*c₀+13)+1
      let s := pairs F δ T A
      let p := fun ij => packet ij S (a ij) (b ij) (c ij) (d ij) (R ij)
      (∑ ij∈s.filter (fun ij =>
        (2-(zero ij.1).re-(zero ij.2).re)*Real.log N < (4+(m+r))*Real.log L ∧
        1 < L^(4+(m+r))*(p ij).productSaving ∧
        1 < L^(4+(m+r))*(p ij).gcdSaving n), ((p ij).value n).re)
        -(2*weightConstant^3)*(N/L^m) ≤
      (∑ q∈S, ∑ ij∈(occurrences F δ T) ×ˢ (occurrences F δ T),
        denominatorTerm ij q n (a ij) (b ij) (c ij) (d ij) (R ij)).re := by
  obtain ⟨K,hK,H⟩ := occurrenceResidual
  refine ⟨K,hK,?_⟩
  intro F A n N T δ c₀ m hA hn hN hT hAN hlog hδ hδ' hcut hc₀ hK2 hF S a b c d R hS hw
  dsimp only
  rw [reindexDenominatorSum F δ T A n S a b c d R hS]
  rw [Complex.re_sum]
  exact H F A n N T δ c₀ m hA hn hN hT hAN hlog hδ hδ' hcut hc₀ hK2 hF S a b c d R hS hw

end
end InnerFloorOccurrence
#print axioms InnerFloorOccurrence.denominatorResidualFloor


/-!
Route B Signed Spectral Core (Standalone Verified Module):
1. Exact finite-sum signed bilinear decomposition (S^2 - M^2) under S = M + g + b,
   preserving all sign cancellation in the bad quadratic and model-bad cross terms
   while absorbing all good-spectrum L2 energy via Cauchy--Schwarz.
2. Exact vanishing of the model-bad cross Gauss sum at q ∣ n for any nonprincipal χ
   and any additive character e.
3. Exact Gauss-sum square identity `gaussSum χ e ^ 2 = χ (-1) * q` for any primitive
   quadratic character and any primitive additive character e, plus exact 3-way parity
   & reality partition of any triple-gate residual Finset.
-/
namespace InnerFloorRouteB
open Finset AddChar MulChar
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Pointwise complex identity for S = M + g + b. -/
theorem sq_sub_sq_split (M g b : ℂ) :
    (M + g + b) ^ 2 - M ^ 2 =
      b ^ 2 + 2 * M * b + (g ^ 2 + 2 * M * g + 2 * b * g) := by
  ring

/-- Finite-sum Cauchy--Schwarz in norm form. -/
theorem sum_norm_mul_le_sqrt {ι : Type*} (s : Finset ι) (u v : ι → ℂ) :
    ∑ i ∈ s, ‖u i‖ * ‖v i‖ ≤
      Real.sqrt (∑ i ∈ s, ‖u i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2) := by
  have h1 : 0 ≤ ∑ i ∈ s, ‖u i‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i ∈ s, ‖v i‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖u i‖) (fun i => ‖v i‖)
  have hnn : 0 ≤ ∑ i ∈ s, ‖u i‖ * ‖v i‖ := sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : (∑ i ∈ s, ‖u i‖ * ‖v i‖) ^ 2 ≤
      (Real.sqrt (∑ i ∈ s, ‖u i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖v i‖ ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2]
    exact hcs
  exact (sq_le_sq₀ hnn (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hsq

/-- Exact signed bilinear lower bound on any finite cell sum weighted by a
    unit-modulus phase e(i).  Only the controlled error g enters through its
    L2 energy; the bad quadratic and model-bad cross terms retain full sign. -/
theorem signedBilinearCellFloor {ι : Type*} (s : Finset ι)
    (M g b e : ι → ℂ) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    (∑ i ∈ s, (b i ^ 2 * e i).re) + 2 * (∑ i ∈ s, (M i * b i * e i).re) -
      ((∑ i ∈ s, ‖g i‖ ^ 2) +
        2 * Real.sqrt (∑ i ∈ s, ‖g i‖ ^ 2) *
          (Real.sqrt (∑ i ∈ s, ‖M i‖ ^ 2) + Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2))) ≤
      ∑ i ∈ s, (((M i + g i + b i) ^ 2 - M i ^ 2) * e i).re := by
  have hsplit :
      (∑ i ∈ s, (((M i + g i + b i) ^ 2 - M i ^ 2) * e i).re) =
        (∑ i ∈ s, (b i ^ 2 * e i).re) + 2 * (∑ i ∈ s, (M i * b i * e i).re) +
          (∑ i ∈ s, ((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    have h1 := sq_sub_sq_split (M i) (g i) (b i)
    rw [h1, add_mul, add_mul, Complex.add_re, Complex.add_re]
    have h2 : (2 * M i * b i * e i).re = 2 * (M i * b i * e i).re := by
      have hm : (2 : ℂ) * M i * b i * e i = ((2 : ℝ) : ℂ) * (M i * b i * e i) := by
        push_cast; ring
      rw [hm, Complex.re_ofReal_mul]
    rw [h2]
  rw [hsplit]
  suffices herr :
      -(∑ i ∈ s, ((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) ≤
        (∑ i ∈ s, ‖g i‖ ^ 2) +
          2 * Real.sqrt (∑ i ∈ s, ‖g i‖ ^ 2) *
            (Real.sqrt (∑ i ∈ s, ‖M i‖ ^ 2) + Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2)) by
    linarith
  have hterm : ∀ i ∈ s,
      -(((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) ≤
        ‖g i‖ ^ 2 + 2 * (‖g i‖ * ‖M i‖) + 2 * (‖g i‖ * ‖b i‖) := by
    intro i hi
    have hre : -(((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) ≤
        ‖(g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i‖ := by
      have habs := Complex.abs_re_le_norm ((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i)
      exact (neg_le_abs _).trans habs
    have hmul : ‖(g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i‖ ≤
        ‖g i ^ 2 + 2 * M i * g i + 2 * b i * g i‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (he i hi)
    have htri : ‖g i ^ 2 + 2 * M i * g i + 2 * b i * g i‖ ≤
        ‖g i‖ ^ 2 + 2 * (‖g i‖ * ‖M i‖) + 2 * (‖g i‖ * ‖b i‖) := by
      calc
        ‖g i ^ 2 + 2 * M i * g i + 2 * b i * g i‖
            ≤ ‖g i ^ 2 + 2 * M i * g i‖ + ‖2 * b i * g i‖ := norm_add_le _ _
        _ ≤ (‖g i ^ 2‖ + ‖2 * M i * g i‖) + ‖2 * b i * g i‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ = ‖g i‖ ^ 2 + 2 * (‖g i‖ * ‖M i‖) + 2 * (‖g i‖ * ‖b i‖) := by
            simp only [norm_pow, norm_mul, Complex.norm_ofNat]
            ring
    exact hre.trans (hmul.trans htri)
  have hsum :
      -(∑ i ∈ s, ((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re) ≤
        (∑ i ∈ s, ‖g i‖ ^ 2) + 2 * (∑ i ∈ s, ‖g i‖ * ‖M i‖) + 2 * (∑ i ∈ s, ‖g i‖ * ‖b i‖) := by
    rw [← sum_neg_distrib]
    calc
      ∑ i ∈ s, -(((g i ^ 2 + 2 * M i * g i + 2 * b i * g i) * e i).re)
          ≤ ∑ i ∈ s, (‖g i‖ ^ 2 + 2 * (‖g i‖ * ‖M i‖) + 2 * (‖g i‖ * ‖b i‖)) :=
          sum_le_sum hterm
      _ = (∑ i ∈ s, ‖g i‖ ^ 2) + 2 * (∑ i ∈ s, ‖g i‖ * ‖M i‖) + 2 * (∑ i ∈ s, ‖g i‖ * ‖b i‖) := by
          simp only [sum_add_distrib, ← mul_sum]
  have hcsM := sum_norm_mul_le_sqrt s g M
  have hcsB := sum_norm_mul_le_sqrt s g b
  nlinarith only [hsum, hcsM, hcsB]

/-- Exact vanishing of the shifted Gauss sum `gaussSum ψ (e.mulShift (-n))`
    when `q ∣ n` and `ψ ≠ 1`. -/
theorem shiftedGauss_nonprincipal_eq_zero_of_dvd {q : ℕ} [NeZero q]
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (e : AddChar (ZMod q) ℂ)
    {n : ℕ} (hdvd : q ∣ n) :
    gaussSum ψ (e.mulShift (-(n : ZMod q))) = 0 := by
  have hzero : (-(n : ZMod q)) = 0 := by
    have hq : (n : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff n q).2 hdvd
    simp [hq]
  rw [hzero]
  unfold gaussSum
  simp only [AddChar.mulShift_apply, zero_mul, AddChar.map_zero_eq_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one hψ

/-- Primitive Gauss-sum product identity for any primitive additive character e. -/
theorem primitive_gaussSum_mul_inv {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) ℂ} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = q := by
  classical
  calc
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹
        = ∑ a : ZMod q, gaussSum χ (e.mulShift a) * e (-a) := by
      simp_rw [gaussSum_mulShift_of_isPrimitive e hχ]
      change gaussSum χ e * (∑ a : ZMod q, χ⁻¹ a * e (-a)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b : ZMod q, χ b * ∑ a : ZMod q, e (a * (b - 1)) := by
      simp only [gaussSum, AddChar.mulShift_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext b
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← e.map_add_eq_mul]
      congr 2
      ring
    _ = q := by
      simp_rw [AddChar.sum_mulShift _ he]
      simp [sub_eq_zero]

/-- Exact Gauss-sum square for any primitive quadratic character:
    `+q` when even (`χ (-1) = 1`), `-q` when odd (`χ (-1) = -1`). -/
theorem primitive_quadratic_gaussSum_sq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod q) ℂ} (he : e.IsPrimitive) :
    gaussSum χ e ^ 2 = χ (-1) * (q : ℂ) := by
  rw [pow_two, ← primitive_gaussSum_mul_inv hχ he, hquad.inv, mul_rotate']
  congr 1
  rw [mul_comm, ← gaussSum_mulShift χ e (-1 : (ZMod q)ˣ), AddChar.inv_mulShift]
  rfl

/-- For every Dirichlet character, `χ (-1) ≠ 1` implies `χ (-1) = -1`. -/
theorem neg_one_eq_neg_one_of_ne_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ (-1) ≠ 1) :
    χ (-1) = -1 := by
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]
    simp
  have hfac : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by
    calc
      (χ (-1) - 1) * (χ (-1) + 1) = χ (-1) * χ (-1) - 1 := by ring
      _ = 1 - 1 := by rw [hsq]
      _ = 0 := sub_self 1
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) hne
  · exact eq_neg_of_add_eq_zero_left h2

/-- Exact 3-way parity & reality partition of any pair Finset. -/
theorem pair_parity_split {α : Type*} (R3 : Finset (α × α))
    (isQuad : α → Prop) (isEven : α → Prop) (f : α × α → ℝ) :
    (∑ ij ∈ R3, f ij) =
      (∑ ij ∈ R3.filter (fun ij => ij.1 = ij.2 ∧ isQuad ij.1 ∧ isEven ij.1), f ij) +
      (∑ ij ∈ R3.filter (fun ij => ij.1 = ij.2 ∧ isQuad ij.1 ∧ ¬isEven ij.1), f ij) +
      (∑ ij ∈ R3.filter (fun ij => ¬(ij.1 = ij.2 ∧ isQuad ij.1)), f ij) := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨x, y⟩ _
  by_cases h1 : x = y
  · subst h1
    by_cases h2 : isQuad x <;> by_cases h3 : isEven x <;> simp [h2, h3]
  · simp [h1]

end
end InnerFloorRouteB

#print axioms InnerFloorRouteB.signedBilinearCellFloor
#print axioms InnerFloorRouteB.shiftedGauss_nonprincipal_eq_zero_of_dvd
#print axioms InnerFloorRouteB.primitive_quadratic_gaussSum_sq
#print axioms InnerFloorRouteB.neg_one_eq_neg_one_of_ne_one
#print axioms InnerFloorRouteB.pair_parity_split


/-!
Route B Research Thresholds & Escape-Hatch Formalization:
1. Even Real Diagonal Positivity: for an even primitive quadratic character
   (`χ (-1) = 1`) and any nonnegative real kernel `w ≥ 0`, both the Gauss-sum
   square `+(q : ℂ)` and the self-convolution `∑ k ≤ n, w k * w (n - k)` are
   nonnegative, so even Siegel zeros contribute positively to the signed floor.
2. Exact Necessity & Sufficiency Threshold for Odd Real Zeros:
   - Necessity (`oddReal_logGap_violates_floor`): at `n = q^k` with `β = 1 - c/log q`,
     `-(q/φ(q)) * n^(2β - 1) ≤ -exp(-2kc) * n`, violating `-εn` for `ε < exp(-2kc)`.
   - Sufficiency (`oddReal_superLogGap_satisfies_floor`): whenever
     `(1 - β) * log n ≥ (1/2) * log (q / (φ(q) * ε))`, we have
     `-(ε * n) ≤ -(q/φ(q)) * n^(2β - 1)`.
3. Almost-All Escape Hatch (`multiples_card_le_div`): the set of `n ∈ Icc 1 X`
   divisible by `d ≥ 1` has cardinality at most `X / d`, explaining formally why
   Gate 3 (`gcdSaving`) eliminates an odd exceptional conductor for almost all
   even `n ≤ X`, whereas the pointwise `∀ n ≥ N, Even n` frozen statement
   cannot avoid `d ∣ n`.
-/
namespace InnerFloorRouteBThreshold
open Finset AddChar MulChar
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Nonnegativity of discrete self-convolution for any nonnegative real kernel. -/
theorem selfConvolution_nonneg (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), w k * w (n - k) :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (hw (n - k))

/-- For an even real diagonal term (positive Gauss-sum factor `q / φ(q)` and
    nonnegative self-convolution), the signed contribution is nonnegative. -/
theorem evenRealDiag_contribution_nonneg (q n : ℕ)
    (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) :
    0 ≤ ((q : ℝ) / (q.totient : ℝ)) * (∑ k ∈ Finset.range (n + 1), w k * w (n - k)) := by
  have hφ : 0 ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg q) hφ) (selfConvolution_nonneg w hw n)

/-- Exact identity `n^(2β - 1) = n * exp(-2 * (1 - β) * log n)` for `n > 0`. -/
theorem rpow_two_beta_sub_one_eq (n β : ℝ) (hn : 0 < n) :
    n ^ (2 * β - 1) = n * Real.exp (-(2 * (1 - β) * Real.log n)) := by
  rw [Real.rpow_def_of_pos hn]
  have h1 : Real.log n * (2 * β - 1) = Real.log n + -(2 * (1 - β) * Real.log n) := by ring
  rw [h1, Real.exp_add, Real.exp_log hn]

/-- Necessity: if `n = q^k` (`q > 1`, `k > 0`) and `β = 1 - c / log q`, then
    the odd real diagonal contribution `-(q/φ(q)) * n^(2β - 1)` is bounded
    above by `-exp(-2kc) * n`, violating `-εn` whenever `ε < exp(-2kc)`. -/
theorem oddReal_logGap_violates_floor (q : ℕ) (hq : 1 < q) (k c ε : ℝ)
    (hε : ε < Real.exp (-(2 * k * c))) :
    let n : ℝ := (q : ℝ) ^ k;
    let β : ℝ := 1 - c / Real.log (q : ℝ);
    -((q : ℝ) / (q.totient : ℝ)) * n ^ (2 * β - 1) < -(ε * n) := by
  dsimp only
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hnp : 0 < (q : ℝ) ^ k := Real.rpow_pos_of_pos hqp k
  have hlogq : Real.log (q : ℝ) ≠ 0 := (Real.log_pos hqR).ne'
  rw [rpow_two_beta_sub_one_eq ((q : ℝ) ^ k) (1 - c / Real.log (q : ℝ)) hnp]
  rw [Real.log_rpow hqp]
  have hexp : -(2 * (1 - (1 - c / Real.log (q : ℝ))) * (k * Real.log (q : ℝ))) = -(2 * k * c) := by
    field_simp
    ring
  rw [hexp]
  have hφp : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hratio : 1 ≤ (q : ℝ) / (q.totient : ℝ) :=
    (le_div_iff₀ hφp).2 (by simpa only [one_mul] using
      (show (q.totient : ℝ) ≤ (q : ℝ) by exact_mod_cast Nat.totient_le q))
  have hepos : 0 < Real.exp (-(2 * k * c)) := Real.exp_pos _
  have h1 : Real.exp (-(2 * k * c)) * (q : ℝ) ^ k ≤
      ((q : ℝ) / (q.totient : ℝ)) * ((q : ℝ) ^ k * Real.exp (-(2 * k * c))) := by
    have hm := mul_le_mul_of_nonneg_right hratio (mul_pos hnp hepos).le
    nlinarith only [hm]
  have h2 : ε * (q : ℝ) ^ k < Real.exp (-(2 * k * c)) * (q : ℝ) ^ k :=
    mul_lt_mul_of_pos_right hε hnp
  linarith only [h1, h2]

/-- Sufficiency: if `(1 - β) * log n ≥ (1/2) * log (q / (φ(q) * ε))` for `n > 0`,
    `q ≥ 1`, `ε > 0`, then the odd real diagonal contribution is absorbed into
    the one-sided floor `-(ε * n)`. -/
theorem oddReal_superLogGap_satisfies_floor (q : ℕ) (hq : 0 < q)
    (n β ε : ℝ) (hn : 0 < n) (hε : 0 < ε)
    (hgap : (1 / 2 : ℝ) * Real.log ((q : ℝ) / ((q.totient : ℝ) * ε)) ≤ (1 - β) * Real.log n) :
    -(ε * n) ≤ -((q : ℝ) / (q.totient : ℝ)) * n ^ (2 * β - 1) := by
  rw [rpow_two_beta_sub_one_eq n β hn]
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hφp : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have harg : 0 < (q : ℝ) / ((q.totient : ℝ) * ε) := by positivity
  have h2 : Real.log ((q : ℝ) / ((q.totient : ℝ) * ε)) ≤ 2 * (1 - β) * Real.log n := by
    linarith only [hgap]
  have hexp : (q : ℝ) / ((q.totient : ℝ) * ε) ≤ Real.exp (2 * (1 - β) * Real.log n) := by
    rw [← Real.exp_log harg]
    exact Real.exp_le_exp.mpr h2
  have hinv : Real.exp (-(2 * (1 - β) * Real.log n)) ≤ (q.totient : ℝ) * ε / (q : ℝ) := by
    rw [Real.exp_neg]
    have hpos : 0 < Real.exp (2 * (1 - β) * Real.log n) := Real.exp_pos _
    rw [inv_le_iff_one_le_mul₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left hexp (div_nonneg (mul_nonneg hφp.le hε.le) hqp.le)
    have hcancel : (q.totient : ℝ) * ε / (q : ℝ) * ((q : ℝ) / ((q.totient : ℝ) * ε)) = 1 := by
      field_simp
    linarith only [hmul, hcancel]
  have hcoeff : ((q : ℝ) / (q.totient : ℝ)) * Real.exp (-(2 * (1 - β) * Real.log n)) ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left hinv (div_nonneg hqp.le hφp.le)
    have hsimp : (q : ℝ) / (q.totient : ℝ) * ((q.totient : ℝ) * ε / (q : ℝ)) = ε := by
      field_simp
    linarith only [hm, hsimp]
  have hn_mul := mul_le_mul_of_nonneg_right hcoeff hn.le
  linarith only [hn_mul]

/-- Almost-all escape hatch: the number of integers `n ∈ Icc 1 X` divisible by
    `d ≥ 1` is at most `X / d`. -/
theorem multiples_card_le_div (X d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 X).filter (fun n => d ∣ n)).card ≤ X / d := by
  have hinj : ∀ a ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
      ∀ b ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n), a / d = b / d → a = b := by
    intro a ha b hb hab
    have hda : d ∣ a := (Finset.mem_filter.mp ha).2
    have hdb : d ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = d * (a / d) := (Nat.mul_div_cancel' hda).symm
      _ = d * (b / d) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hdb
  have hmaps : ∀ a ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n),
      a / d ∈ Finset.Icc 1 (X / d) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hrange := Finset.mem_Icc.mp ha'.1
    have hda : d ∣ a := ha'.2
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hrange.2⟩
    rcases hda with ⟨k, rfl⟩
    have hk : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      omega
    rw [Nat.mul_div_right k hd]
    exact hk
  calc
    ((Finset.Icc 1 X).filter (fun n => d ∣ n)).card
        ≤ (Finset.Icc 1 (X / d)).card := Finset.card_le_card_of_injOn (fun a => a / d) hmaps hinj
    _ = X / d := by simp

end
end InnerFloorRouteBThreshold

#print axioms InnerFloorRouteBThreshold.selfConvolution_nonneg
#print axioms InnerFloorRouteBThreshold.evenRealDiag_contribution_nonneg
#print axioms InnerFloorRouteBThreshold.oddReal_logGap_violates_floor
#print axioms InnerFloorRouteBThreshold.oddReal_superLogGap_satisfies_floor
#print axioms InnerFloorRouteBThreshold.multiples_card_le_div


/-!
Route B Unconditional Almost-All Even n Closure (Gate-3 Exceptional Set Density):
Proves that for any finite family of exceptional conductors `D` and any
Gate-3 threshold `M > 0`, the set of integers `n ∈ Icc 1 X` whose gcd ratio
`gcd(n, d) / d` exceeds `1 / M` for some `d ∈ D` has cardinality bounded by
`∑ d ∈ D, ∑ g ∈ d.divisors with d < g * M, (X / g)`, and in real-valued form by
`(X : ℝ) * M * ∑ d ∈ D, (d.divisors.card : ℝ) / (d : ℝ)`.

Consequently, even without ruling out hypothetical odd Siegel zeros or q-aspect
log-gap zeros, Gate 3 (`gcdSaving`) eliminates the entire triple-gate residual
for all `n ≤ X` outside an explicit exceptional set of density
`O(M * ∑_{d ∈ D} τ(d) / d)`.
-/
namespace InnerFloorRouteBAlmostAll
open Finset
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Number of integers `n ∈ Icc 1 X` divisible by `g > 0` is at most `X / g`. -/
theorem multiples_card_le_div (X g : ℕ) (hg : 0 < g) :
    ((Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)).card ≤ X / g := by
  have hinj : ∀ a ∈ (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n),
      ∀ b ∈ (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n), a / g = b / g → a = b := by
    intro a ha b hb hab
    have hga : g ∣ a := (Finset.mem_filter.mp ha).2
    have hgb : g ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = g * (a / g) := (Nat.mul_div_cancel' hga).symm
      _ = g * (b / g) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hgb
  have hmaps : ∀ a ∈ (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n),
      a / g ∈ Finset.Icc 1 (X / g) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hrange := Finset.mem_Icc.mp ha'.1
    have hga : g ∣ a := ha'.2
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hrange.2⟩
    rcases hga with ⟨k, rfl⟩
    have hk : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      omega
    rw [Nat.mul_div_right k hg]
    exact hk
  calc
    ((Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)).card
        ≤ (Finset.Icc 1 (X / g)).card := Finset.card_le_card_of_injOn (fun a => a / g) hmaps hinj
    _ = X / g := by simp

/-- High-gcd exceptional set for a single conductor `d` and real threshold `M`:
    all `n ∈ Icc 1 X` such that `(d : ℝ) < (Nat.gcd n d : ℝ) * M`. -/
def highGcdSet (X d : ℕ) (M : ℝ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => (d : ℝ) < (Nat.gcd n d : ℝ) * M)

/-- Every `n ∈ highGcdSet X d M` is divisible by some divisor `g ∣ d`
    satisfying `(d : ℝ) < (g : ℝ) * M`. -/
theorem highGcdSet_subset_biUnion (X d : ℕ) (hd : 0 < d) (M : ℝ) :
    highGcdSet X d M ⊆
      (d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M)).biUnion
        (fun g => (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)) := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  refine Finset.mem_biUnion.mpr ⟨Nat.gcd n d, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n d, hd.ne'⟩, hn'.2⟩
  · exact Finset.mem_filter.mpr ⟨hn'.1, Nat.gcd_dvd_left n d⟩

/-- Exact combinatorial bound for a single conductor `d`:
    `|highGcdSet X d M| ≤ ∑_{g ∣ d, d < g * M} (X / g)`. -/
theorem highGcdSet_card_le_sum_div (X d : ℕ) (hd : 0 < d) (M : ℝ) :
    (highGcdSet X d M).card ≤
      ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), X / g := by
  calc
    (highGcdSet X d M).card
        ≤ ((d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M)).biUnion
            (fun g => (Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n))).card :=
          Finset.card_le_card (highGcdSet_subset_biUnion X d hd M)
    _ ≤ ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M),
          ((Finset.Icc 1 X).filter (fun n : ℕ => g ∣ n)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), X / g := by
          apply Finset.sum_le_sum
          intro g hg
          have hgd : g ∣ d := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
          have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgd hd
          exact multiples_card_le_div X g hgpos

/-- Real-valued density bound for a single conductor `d > 0` and `M ≥ 0`:
    `|highGcdSet X d M| ≤ X * M * τ(d) / d`. -/
theorem highGcdSet_card_le_real (X d : ℕ) (hd : 0 < d) (M : ℝ) (hM : 0 ≤ M) :
    ((highGcdSet X d M).card : ℝ) ≤ (X : ℝ) * M * (d.divisors.card : ℝ) / (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((highGcdSet X d M).card : ℝ) ≤
      ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), ((X / g : ℕ) : ℝ) := by
    simpa only [Nat.cast_sum] using (show ((highGcdSet X d M).card : ℝ) ≤ ((∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), X / g : ℕ) : ℝ) by exact_mod_cast highGcdSet_card_le_sum_div X d hd M)
  have hterm : ∀ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M),
      ((X / g : ℕ) : ℝ) ≤ (X : ℝ) * M / (d : ℝ) := by
    intro g hg
    have hgd : g ∣ d := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
    have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgd hd
    have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
    have hlt : (d : ℝ) < (g : ℝ) * M := (Finset.mem_filter.mp hg).2
    have hdiv : ((X / g : ℕ) : ℝ) ≤ (X : ℝ) / (g : ℝ) := by
      rw [le_div_iff₀ hgR]
      exact_mod_cast Nat.div_mul_le_self X g
    have hinv : (X : ℝ) / (g : ℝ) ≤ (X : ℝ) * M / (d : ℝ) := by
      rw [div_le_div_iff₀ hgR hdR]
      have hmul := mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg (α := ℝ) X)
      linarith only [hmul]
    exact hdiv.trans hinv
  calc
    ((highGcdSet X d M).card : ℝ)
        ≤ ∑ g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), ((X / g : ℕ) : ℝ) := h1
    _ ≤ ∑ _g ∈ d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M), ((X : ℝ) * M / (d : ℝ)) :=
          Finset.sum_le_sum hterm
    _ = ((d.divisors.filter (fun g : ℕ => (d : ℝ) < (g : ℝ) * M)).card : ℝ) * ((X : ℝ) * M / (d : ℝ)) := by
          simp
    _ ≤ (d.divisors.card : ℝ) * ((X : ℝ) * M / (d : ℝ)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_filter_le d.divisors _
          · positivity
    _ = (X : ℝ) * M * (d.divisors.card : ℝ) / (d : ℝ) := by ring

/-- Family-wide almost-all exceptional set bound:
    for any finite family `D` of positive conductors and threshold `M ≥ 0`,
    the number of integers `n ∈ Icc 1 X` that fail Gate 3 for at least one `d ∈ D`
    is at most `X * M * ∑_{d ∈ D} τ(d) / d`. -/
theorem familyHighGcd_card_le_real (X : ℕ) (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d)
    (M : ℝ) (hM : 0 ≤ M) :
    (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ) ≤
      (X : ℝ) * M * (∑ d ∈ D, (d.divisors.card : ℝ) / (d : ℝ)) := by
  have hsub :
      (Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M) ⊆
        D.biUnion (fun d => highGcdSet X d M) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    rcases hn'.2 with ⟨d, hd, hlt⟩
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨hn'.1, hlt⟩⟩
  have hcard :
      (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ) ≤
        ∑ d ∈ D, ((highGcdSet X d M).card : ℝ) := by
    have hnat :
        ((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card ≤
          ∑ d ∈ D, (highGcdSet X d M).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    simpa only [Nat.cast_sum] using (show (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ) ≤ ((∑ d ∈ D, (highGcdSet X d M).card : ℕ) : ℝ) by exact_mod_cast hnat)
  calc
    (((Finset.Icc 1 X).filter (fun n => ∃ d ∈ D, (d : ℝ) < (Nat.gcd n d : ℝ) * M)).card : ℝ)
        ≤ ∑ d ∈ D, ((highGcdSet X d M).card : ℝ) := hcard
    _ ≤ ∑ d ∈ D, ((X : ℝ) * M * ((d.divisors.card : ℝ) / (d : ℝ))) := by
          apply Finset.sum_le_sum
          intro d hd
          simpa only [mul_div_assoc] using highGcdSet_card_le_real X d (hD d hd) M hM
    _ = (X : ℝ) * M * (∑ d ∈ D, (d.divisors.card : ℝ) / (d : ℝ)) := by
          rw [Finset.mul_sum]

end
end InnerFloorRouteBAlmostAll

#print axioms InnerFloorRouteBAlmostAll.multiples_card_le_div
#print axioms InnerFloorRouteBAlmostAll.highGcdSet_card_le_sum_div
#print axioms InnerFloorRouteBAlmostAll.highGcdSet_card_le_real
#print axioms InnerFloorRouteBAlmostAll.familyHighGcd_card_le_real


/-!
Route B Four-Gate Residual & Joint Gauss--Ramanujan Sign Obstruction:
1. `fourGateResidualPartition`: extends the 3-gate quantitative residual partition
   to FOUR independent attenuation gates:
   - Gate 1: real-part deficit `(2 - β₁ - β₂) * log N ≥ (4 + m + r) * log L`
   - Gate 2: product conductor saving `L^(4 + m + r) * prodSav ≤ 1`
   - Gate 3: gcd ratio saving `L^(4 + m + r) * gcdSav ≤ 1`
   - Gate 4 (NEW): imaginary height saving `L^(4 + m + r) * heightSav ≤ 1`
2. `jointSign_even_countermodel_neg`: exact arithmetic coefficient bound
   `3p * (-(p-1)) / (2*(p-1))^2 = -3p / (4*(p-1)) ≤ -3/4` for the even
   conductor `d = 3p` (`p ≡ 3 (mod 4)`, `n = 2p^8`) countermodel.
3. `global_mod3_forced_one` & `global_parity_annihilation_mod_3p`: proves that
   for ANY prime `p ≠ 3` and ANY `p₁ + p₂ = 2p^8` with `3 ∤ p₁`, `3 ∤ p₂`,
   we necessarily have `p₁ ≡ 1 (mod 3)`, `p₂ ≡ 1 (mod 3)`, and `p₁ ≡ -p₂ (mod p)` —
   so an even composite Siegel character `χ = χ₃ * χ_p` (`χ₃` odd, `χ_p` odd)
   forces `χ(p₁) = -χ(p₂)` globally, annihilating Goldbach representations
   just like an odd character at `d ∣ n`.
-/
namespace InnerFloorRouteBFourGate
open Finset
open scoped Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- Four-gate quantitative residual partition: any index in `s` that clears
    at least one of the 4 gates (real-part, product conductor, gcd ratio, or
    imaginary height) contributes at most `C * N / L^(m + r)`, so with
    `|s| ≤ L^r` all cleared terms sum to at most `C * N / L^m`. -/
theorem fourGateResidualPartition {ι : Type*} (s : Finset ι)
    (val : ι → ℂ) (β₁ β₂ prodSav gcdSav heightSav : ι → ℝ)
    (N L C k r m : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ L ^ r)
    (hβ : ∀ i ∈ s, β₁ i + β₂ i ≤ 2)
    (hprod0 : ∀ i ∈ s, 0 ≤ prodSav i)
    (hgcd0 : ∀ i ∈ s, 0 ≤ gcdSav i)
    (hht0 : ∀ i ∈ s, 0 ≤ heightSav i)
    (hb_re : ∀ i ∈ s, ‖val i‖ ≤ C * N ^ (β₁ i + β₂ i - 1) * L ^ k)
    (hb_prod : ∀ i ∈ s, ‖val i‖ ≤ C * N * L ^ k * prodSav i)
    (hb_gcd : ∀ i ∈ s, ‖val i‖ ≤ C * N * L ^ k * gcdSav i)
    (hb_ht : ∀ i ∈ s, ‖val i‖ ≤ C * N * L ^ k * heightSav i) :
    let R4 := s.filter (fun i =>
      (2 - β₁ i - β₂ i) * Real.log N < (k + (m + r)) * Real.log L ∧
      1 < L ^ (k + (m + r)) * prodSav i ∧
      1 < L ^ (k + (m + r)) * gcdSav i ∧
      1 < L ^ (k + (m + r)) * heightSav i)
    (∑ i ∈ R4, (val i).re) - C * (N / L ^ m) ≤ ∑ i ∈ s, (val i).re := by
  dsimp only
  set P : ι → Prop := fun i =>
    (2 - β₁ i - β₂ i) * Real.log N < (k + (m + r)) * Real.log L ∧
    1 < L ^ (k + (m + r)) * prodSav i ∧
    1 < L ^ (k + (m + r)) * gcdSav i ∧
    1 < L ^ (k + (m + r)) * heightSav i
  have hNp : 0 < N := by linarith
  have hLpos : 0 < L ^ (m + r) := Real.rpow_pos_of_pos hL _
  have hsplit : (∑ i ∈ s, (val i).re) =
      (∑ i ∈ s.filter P, (val i).re) + (∑ i ∈ s.filter (fun i => ¬P i), (val i).re) :=
    (Finset.sum_filter_add_sum_filter_not s P (fun i => (val i).re)).symm
  rw [hsplit]
  suffices htail : -(∑ i ∈ s.filter (fun i => ¬P i), (val i).re) ≤ C * (N / L ^ m) by
    linarith
  have hterm : ∀ i ∈ s.filter (fun i => ¬P i),
      -(val i).re ≤ C * N / L ^ (m + r) := by
    intro i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hnot : ¬P i := (Finset.mem_filter.mp hi).2
    have hre : -(val i).re ≤ ‖val i‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    have hnorm : ‖val i‖ ≤ C * N / L ^ (m + r) := by
      have hLk : L ^ k / L ^ (k + (m + r)) = 1 / L ^ (m + r) := by
        rw [Real.rpow_add hL]
        field_simp
      by_cases h1 : (k + (m + r)) * Real.log L ≤ (2 - β₁ i - β₂ i) * Real.log N
      · have hexp : N ^ (β₁ i + β₂ i - 1) ≤ N / L ^ (k + (m + r)) := by
          have h1' : Real.log (L ^ (k + (m + r))) ≤ Real.log (N ^ (2 - β₁ i - β₂ i)) := by
            rw [Real.log_rpow hL, Real.log_rpow hNp]
            exact h1
          have h2 : L ^ (k + (m + r)) ≤ N ^ (2 - β₁ i - β₂ i) := by
            rw [← Real.exp_log (Real.rpow_pos_of_pos hL _),
                ← Real.exp_log (Real.rpow_pos_of_pos hNp _)]
            exact Real.exp_le_exp.mpr h1'
          rw [le_div_iff₀ (Real.rpow_pos_of_pos hL _)]
          calc
            N ^ (β₁ i + β₂ i - 1) * L ^ (k + (m + r))
                ≤ N ^ (β₁ i + β₂ i - 1) * N ^ (2 - β₁ i - β₂ i) :=
                  mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hNp.le _)
            _ = N ^ ((β₁ i + β₂ i - 1) + (2 - β₁ i - β₂ i)) := (Real.rpow_add hNp _ _).symm
            _ = N := by
                  have ha : (β₁ i + β₂ i - 1) + (2 - β₁ i - β₂ i) = 1 := by ring
                  rw [ha, Real.rpow_one]
        calc
          ‖val i‖ ≤ C * N ^ (β₁ i + β₂ i - 1) * L ^ k := hb_re i his
          _ ≤ C * (N / L ^ (k + (m + r))) * L ^ k := by
                have hm := mul_le_mul_of_nonneg_left hexp hC
                exact mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hL.le _)
          _ = C * N * (L ^ k / L ^ (k + (m + r))) := by ring
          _ = C * N / L ^ (m + r) := by rw [hLk]; ring
      · by_cases h2 : L ^ (k + (m + r)) * prodSav i ≤ 1
        · have hsav : prodSav i ≤ 1 / L ^ (k + (m + r)) :=
            (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).2 (by linarith)
          calc
            ‖val i‖ ≤ C * N * L ^ k * prodSav i := hb_prod i his
            _ ≤ C * N * L ^ k * (1 / L ^ (k + (m + r))) :=
                  mul_le_mul_of_nonneg_left hsav (by positivity)
            _ = C * N * (L ^ k / L ^ (k + (m + r))) := by ring
            _ = C * N / L ^ (m + r) := by rw [hLk]; ring
        · by_cases h3 : L ^ (k + (m + r)) * gcdSav i ≤ 1
          · have hsav : gcdSav i ≤ 1 / L ^ (k + (m + r)) :=
              (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).2 (by linarith)
            calc
              ‖val i‖ ≤ C * N * L ^ k * gcdSav i := hb_gcd i his
              _ ≤ C * N * L ^ k * (1 / L ^ (k + (m + r))) :=
                    mul_le_mul_of_nonneg_left hsav (by positivity)
              _ = C * N * (L ^ k / L ^ (k + (m + r))) := by ring
              _ = C * N / L ^ (m + r) := by rw [hLk]; ring
          · have h4 : L ^ (k + (m + r)) * heightSav i ≤ 1 := by
              by_contra hc
              exact hnot ⟨lt_of_not_ge h1, lt_of_not_ge h2, lt_of_not_ge h3, lt_of_not_ge hc⟩
            have hsav : heightSav i ≤ 1 / L ^ (k + (m + r)) :=
              (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).2 (by linarith)
            calc
              ‖val i‖ ≤ C * N * L ^ k * heightSav i := hb_ht i his
              _ ≤ C * N * L ^ k * (1 / L ^ (k + (m + r))) :=
                    mul_le_mul_of_nonneg_left hsav (by positivity)
              _ = C * N * (L ^ k / L ^ (k + (m + r))) := by ring
              _ = C * N / L ^ (m + r) := by rw [hLk]; ring
    exact hre.trans hnorm
  rw [← Finset.sum_neg_distrib]
  calc
    ∑ i ∈ s.filter (fun i => ¬P i), -(val i).re
        ≤ ∑ _i ∈ s.filter (fun i => ¬P i), (C * N / L ^ (m + r)) := Finset.sum_le_sum hterm
    _ = ((s.filter (fun i => ¬P i)).card : ℝ) * (C * N / L ^ (m + r)) := by simp
    _ ≤ (s.card : ℝ) * (C * N / L ^ (m + r)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_filter_le s _
          · positivity
    _ ≤ L ^ r * (C * N / L ^ (m + r)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C * (N / L ^ m) := by
          rw [Real.rpow_add hL]
          field_simp

/-- Exact negative arithmetic factor for GPT's even countermodel `d = 3p`,
    `p > 3`, `n = 2p^8`: `(3p) * (-(p-1)) / (2(p-1))^2 = -3p / (4(p-1)) ≤ -3/4`. -/
theorem jointSign_even_countermodel_neg (p : ℕ) (hp : 3 < p) :
    ((3 * p : ℝ) * (-(p - 1 : ℝ))) / ((2 * (p - 1 : ℝ)) ^ 2) ≤ -(3 / 4 : ℝ) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (3 : ℝ) < p := by exact_mod_cast hp
    linarith
  have hEq : ((3 * p : ℝ) * (-(p - 1 : ℝ))) / ((2 * (p - 1 : ℝ)) ^ 2) =
      -(3 * (p : ℝ)) / (4 * ((p : ℝ) - 1)) := by
    field_simp
    ring
  rw [hEq, div_le_iff₀ (by positivity : 0 < 4 * ((p : ℝ) - 1))]
  linarith

/-- Global parity annihilation for `n = 2p^8` (`3 ∤ p`): any two naturals
    `p₁, p₂` coprime to `3` with `p₁ + p₂ = 2p^8` MUST both satisfy `≡ 1 (mod 3)`
    and `p₁ ≡ -p₂ (mod p)`.  Hence `χ₃(p₁) = χ₃(p₂) = 1` while `χ_p(p₁) = -χ_p(p₂)`
    for odd `χ_p`, forcing `χ(p₁) = -χ(p₂)` even though `χ = χ₃ * χ_p` is EVEN! -/
theorem global_mod3_forced_one (p p₁ p₂ : ℕ) (hp3 : ¬(3 ∣ p))
    (h1 : ¬(3 ∣ p₁)) (h2 : ¬(3 ∣ p₂)) (hsum : p₁ + p₂ = 2 * p ^ 8) :
    p₁ % 3 = 1 ∧ p₂ % 3 = 1 := by
  have hmodp : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have hp8 : (p ^ 8) % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmodp with h | h <;> simp [h]
  have h2p8 : (2 * p ^ 8) % 3 = 2 := by
    rw [Nat.mul_mod, hp8]
  have hsum3 : (p₁ + p₂) % 3 = 2 := by rw [hsum, h2p8]
  omega

theorem global_modp_neg (p p₁ p₂ : ℕ) (hsum : p₁ + p₂ = 2 * p ^ 8) :
    ((p₁ : ZMod p) = -((p₂ : ZMod p))) := by
  have hcast : ((p₁ + p₂ : ℕ) : ZMod p) = ((2 * p ^ 8 : ℕ) : ZMod p) :=
    congrArg (Nat.cast : ℕ → ZMod p) hsum
  have hzero : ((2 * p ^ 8 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact ⟨2 * p ^ 7, by ring⟩
  rw [Nat.cast_add, hzero] at hcast
  exact eq_neg_of_add_eq_zero_left hcast

end
end InnerFloorRouteBFourGate

#print axioms InnerFloorRouteBFourGate.fourGateResidualPartition
#print axioms InnerFloorRouteBFourGate.jointSign_even_countermodel_neg
#print axioms InnerFloorRouteBFourGate.global_mod3_forced_one
#print axioms InnerFloorRouteBFourGate.global_modp_neg


namespace InnerFloorIndependentEulerMass
open Finset
noncomputable section

/-- A telescoping majorant for the reciprocal squares of the predecessor
of every odd integer greater than one. -/
theorem oddIndexMass (M : ℕ) :
    (∑ j ∈ range M, 1/(4*((j:ℝ)+1)^2)) ≤ (1/2:ℝ) := by
  have htel : (∑ j ∈ range M, 1/((2*(j:ℝ)+1)*(2*(j:ℝ)+3))) =
      (1/2:ℝ)*(1-1/(2*(M:ℝ)+1)) := by
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [sum_range_succ,ih,Nat.cast_succ]
      have h : (0:ℝ)≤(M:ℝ) := Nat.cast_nonneg M
      field_simp; ring
  calc
    _ ≤ ∑ j ∈ range M, 1/((2*(j:ℝ)+1)*(2*(j:ℝ)+3)) := by
      apply sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ = _ := htel
    _ ≤ _ := by
      have h : (0:ℝ)≤1/(2*(M:ℝ)+1) := by positivity
      linarith

/-- The absolute tail over all nonempty subsets of a finite prime-index
family is below 2/3 when the total local mass is at most 1/2. -/
theorem subsetTailMass {ι : Type*} [DecidableEq ι] (P : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ P, 0≤a i) (hS : ∑ i ∈ P,a i ≤ (1/2:ℝ)) :
    (∑ t ∈ P.powerset.erase ∅, ∏ i ∈ t,a i) ≤ (2/3:ℝ) := by
  have hp : (∏ i ∈ P, (1+a i)) ≤ Real.exp (∑ i ∈ P,a i) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun i hi => by linarith [ha i hi])
      (fun i hi => by simpa [add_comm] using Real.add_one_le_exp (a i))
  have hE : Real.exp (1/2:ℝ) < 5/3 := by
    have h2 : Real.exp (1/2:ℝ)^2 = Real.exp 1 := by
      rw [pow_two,←Real.exp_add]
      norm_num
    have h3 : Real.exp 1 < (25/9:ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    by_contra! h
    nlinarith only [h2,h3,mul_le_mul h h (by norm_num : (0:ℝ)≤5/3) (Real.exp_nonneg _)]
  have hwhole : (∑ t ∈ P.powerset, ∏ i ∈ t,a i) < (5/3:ℝ) := by
    rw [← prod_one_add]
    exact hp.trans_lt ((Real.exp_le_exp.mpr hS).trans_lt hE)
  have he : (∅ : Finset ι) ∈ P.powerset := by simp
  have hs := sum_erase_add P.powerset (fun t => ∏ i ∈ t,a i) he
  simp only [prod_empty] at hs
  linarith only [hs,hwhole]

/-- The actual finite family of odd squarefree cofactors m>1 has a
uniform absolute reciprocal totient-square tail at most 2/3. -/
theorem oddSquarefreeTotientTail (M : ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, 1<m ∧ m≤M ∧ Odd m ∧ Squarefree m) :
    (∑ m ∈ S, 1/((m.totient:ℝ)^2)) ≤ (2/3:ℝ) := by
  let P := (range M).image (fun j : ℕ => 2*j+3)
  let a := fun p : ℕ => 1/((p:ℝ)-1)^2
  have hP : ∑ p ∈ P,a p ≤ (1/2:ℝ) := by
    unfold P
    rw [sum_image (by intro i hi j hj h; change 2*i+3=2*j+3 at h; omega)]
    calc
      _ = ∑ j ∈ range M,1/(4*((j:ℝ)+1)^2) := by
        apply sum_congr rfl
        intro j hj
        dsimp [a]
        push_cast
        congr 1
        ring
      _ ≤ _ := oddIndexMass M
  have htail := subsetTailMass P a (fun i hi => by dsimp [a]; positivity) hP
  have hsub : S.image Nat.primeFactors ⊆ P.powerset.erase ∅ := by
    intro t ht
    obtain ⟨m,hm,rfl⟩ := mem_image.mp ht
    obtain ⟨hm1,hmM,hmodd,hsq⟩ := hS m hm
    apply mem_erase.mpr
    refine ⟨?_,mem_powerset.mpr ?_⟩
    · intro he
      have h := Nat.prod_primeFactors_of_squarefree hsq
      rw [he,prod_empty] at h
      omega
    · intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hd := Nat.dvd_of_mem_primeFactors hp
      have hpM := (Nat.le_of_dvd (by omega : 0<m) hd).trans hmM
      have hpn : ¬2∣p := by
        intro hp2
        obtain ⟨k,hk⟩ := hp2.trans hd
        obtain ⟨l,hl⟩ := hmodd
        omega
      have hpodd : p%2=1 := by omega
      have h2 := hprime.two_le
      have h3 : 3≤p := by omega
      apply mem_image.mpr
      refine ⟨(p-3)/2,mem_range.mpr (by omega),?_⟩
      omega
  have hinj : Set.InjOn Nat.primeFactors (S: Set ℕ) := by
    intro m hm k hk he
    have h1 := Nat.prod_primeFactors_of_squarefree (hS m hm).2.2.2
    have h2 := Nat.prod_primeFactors_of_squarefree (hS k hk).2.2.2
    rw [he] at h1
    exact h1.symm.trans h2
  have hterm (m : ℕ) (hm : m∈S) :
      1/((m.totient:ℝ)^2) = ∏ p ∈ m.primeFactors,a p := by
    obtain ⟨hm1,hmM,hmodd,hsq⟩ := hS m hm
    have hphi := Nat.totient_mul_prod_primeFactors m
    rw [Nat.prod_primeFactors_of_squarefree hsq,mul_comm m] at hphi
    have hφ : m.totient = ∏ p∈m.primeFactors,(p-1) :=
      Nat.eq_of_mul_eq_mul_right (show 0<m by omega) hphi
    rw [hφ,Nat.cast_prod,← Finset.prod_pow]
    calc
      1 / (∏ p ∈ m.primeFactors, ((p-1:ℕ):ℝ)^2) =
          (∏ p ∈ m.primeFactors, (1:ℝ)) / (∏ p ∈ m.primeFactors, ((p-1:ℕ):ℝ)^2) := by simp
      _ = ∏ p ∈ m.primeFactors, a p := by
        rw [← Finset.prod_div_distrib]
        apply prod_congr rfl
        intro p hp
        have hp1 := (Nat.prime_of_mem_primeFactors hp).one_lt.le
        dsimp [a]
        rw [Nat.cast_sub hp1,Nat.cast_one]
  calc
    _ = ∑ m ∈ S,∏ p∈m.primeFactors,a p := sum_congr rfl hterm
    _ = ∑ t ∈ S.image Nat.primeFactors,∏ p∈t,a p := by
      rw [sum_image hinj]
    _ ≤ ∑ t ∈ P.powerset.erase ∅,∏ p∈t,a p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun t ht hnot => prod_nonneg (fun p hp => by dsimp [a]; positivity))
    _ ≤ _ := htail

end
end InnerFloorIndependentEulerMass
#print axioms InnerFloorIndependentEulerMass.oddIndexMass
#print axioms InnerFloorIndependentEulerMass.subsetTailMass

#print axioms InnerFloorIndependentEulerMass.oddSquarefreeTotientTail


namespace InnerFloorIndependentCross
noncomputable section

/-- Arithmetic conductor decay plus the constant real-zero gap yields an
arbitrarily large inverse-log saving. L is log of the target integer.
This is a scalar lemma, not a statement about a Dirichlet L-function. -/
theorem crossSaving (d L c k gap : ℝ)
    (hd : 1≤d) (hL : 1≤L) (hk : 0≤k) (hg : 0≤gap)
    (hgap : c≤gap*Real.log (d+2))
    (hbudget : k*Real.log L*(Real.log 3+2*k*Real.log L)≤c*L) :
    d^(-(1/2):ℝ)*Real.exp (-gap*L) ≤ L^(-k) := by
  have hdp : 0<d := by linarith
  have hLp : 0<L := by linarith
  have hld : 0≤Real.log d := Real.log_nonneg hd
  have hlL : 0≤Real.log L := Real.log_nonneg hL
  rw [Real.rpow_def_of_pos hdp,Real.rpow_def_of_pos hLp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  by_cases h : L^(2*k)≤d
  · have hlog := Real.log_le_log (Real.rpow_pos_of_pos hLp _) h
    rw [Real.log_rpow hLp] at hlog
    nlinarith only [hlog,mul_nonneg hg hLp.le]
  · have hpow : 1≤L^(2*k) := Real.one_le_rpow hL (by linarith)
    have hsmall : d+2≤3*L^(2*k) := by linarith [le_of_not_ge h]
    have hlog := Real.log_le_log (show 0<d+2 by linarith) hsmall
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (Real.rpow_pos_of_pos hLp _).ne',Real.log_rpow hLp] at hlog
    have h1 : k*Real.log L*Real.log (d+2)≤c*L :=
      (mul_le_mul_of_nonneg_left hlog (mul_nonneg hk hlL)).trans hbudget
    have h2 : c*L≤(gap*Real.log (d+2))*L := mul_le_mul_of_nonneg_right hgap hLp.le
    have h3 : k*Real.log L≤gap*L := by
      by_contra! hn
      have hh := mul_lt_mul_of_pos_right hn (Real.log_pos (show 1<d+2 by linarith))
      nlinarith only [h1,h2,hh]
    nlinarith only [h3,hld]

/-- Explicit sufficient budget in the preceding lemma, avoiding any
assumption about rates hidden in an asymptotic notation. -/
theorem crossBudget (L c k : ℝ) (hL : 1≤L) (hc : 0<c) (hk : 0≤k)
    (hlarge : (8*k+32*k^2)/c≤Real.sqrt L) :
    k*Real.log L*(Real.log 3+2*k*Real.log L)≤c*L := by
  let x := Real.sqrt (Real.sqrt L)
  have hL0 : 0≤L := by linarith
  have hx2 : x^2=Real.sqrt L := Real.sq_sqrt (Real.sqrt_nonneg L)
  have hx4 : x^4=L := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,hx2,Real.sq_sqrt hL0]
  have hxs : 1≤x := by
    have h1 : 1≤Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
    exact by simpa [x] using Real.sqrt_le_sqrt h1
  have hxp : 0<x := by linarith
  have hl : 0≤Real.log L := Real.log_nonneg hL
  have hl4 : Real.log L≤4*x := by
    rw [←hx4,Real.log_pow]
    norm_num
    linarith [Real.log_le_sub_one_of_pos hxp]
  have h3 : Real.log 3≤2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  have ht : Real.log 3+2*k*Real.log L≤2+8*k*x := by nlinarith only [h3,mul_le_mul_of_nonneg_left hl4 hk]
  have hb : 0≤Real.log 3+2*k*Real.log L := by
    have := Real.log_nonneg (by norm_num : (1:ℝ)≤3)
    positivity
  have hbound : k*Real.log L*(Real.log 3+2*k*Real.log L)≤(8*k+32*k^2)*x^2 := by
    calc
      _ ≤ (k*(4*x))*(2+8*k*x) := mul_le_mul (mul_le_mul_of_nonneg_left hl4 hk) ht hb (by positivity)
      _ = 8*k*x+32*k^2*x^2 := by ring
      _ ≤ (8*k+32*k^2)*x^2 := by nlinarith only [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8) hk) (mul_nonneg hxp.le (sub_nonneg.mpr hxs))]
  have hcoef : 8*k+32*k^2≤c*Real.sqrt L := by
    have hh := (div_le_iff₀ hc).mp hlarge
    simpa [mul_comm] using hh
  calc
    _ ≤ _ := hbound
    _ ≤ c*Real.sqrt L*x^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
    _ = c*L := by rw [hx2,mul_assoc,←pow_two,Real.sq_sqrt hL0]

/-- All sufficiently large L satisfy the explicit scalar budget. -/
theorem eventualCrossSaving (c k : ℝ) (hc : 0<c) (hk : 0≤k) :
    ∃ L₀ : ℝ, 1≤L₀ ∧ ∀ L≥L₀, ∀ d gap : ℝ,
      1≤d → 0≤gap → c≤gap*Real.log (d+2) →
      d^(-(1/2):ℝ)*Real.exp (-gap*L)≤L^(-k) := by
  let a := max 1 ((8*k+32*k^2)/c)
  have ha : 1≤a := le_max_left _ _
  have ha0 : 0≤a := by linarith
  refine ⟨a^2,by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha)],?_⟩
  intro L hL d gap hd hg hgap
  have hL1 : 1≤L := (show 1≤a^2 by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha)]).trans hL
  have hs := Real.sqrt_le_sqrt hL
  rw [Real.sqrt_sq_eq_abs,abs_of_nonneg ha0] at hs
  exact crossSaving d L c k gap hd hL1 hk hg hgap
    (crossBudget L c k hL1 hc hk ((le_max_right _ _).trans hs))

end
end InnerFloorIndependentCross
#print axioms InnerFloorIndependentCross.crossSaving
#print axioms InnerFloorIndependentCross.crossBudget
#print axioms InnerFloorIndependentCross.eventualCrossSaving


namespace InnerFloorIndependentRealKernel
noncomputable section
open MeasureTheory
open scoped Interval

/-- Exact normalized L2-distance for the near-one power kernel versus one. -/
theorem powerKernel_sq_integral (b : ℝ) (hb : 1/2<b) :
    (∫ x in (0:ℝ)..1,(x^(b-1)-1)^2) =
      2*(1-b)^2/(b*(2*b-1)) := by
  have h1 : -1 < b-1 := by linarith
  have h2 : -1 < 2*b-2 := by linarith
  have hi1 : IntervalIntegrable (fun x:ℝ => x^(b-1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' h1
  have hi2 : IntervalIntegrable (fun x:ℝ => x^(2*b-2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' h2
  have hi0 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 := intervalIntegrable_const
  have he : (∫ x in (0:ℝ)..1,(x^(b-1)-1)^2) =
      ∫ x in (0:ℝ)..1, x^(2*b-2)-2*x^(b-1)+1 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0≤x := by simpa [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx.1
    have hpow : (x^(b-1))^2=x^(2*b-2) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hx0]
      congr 1
      norm_num
      ring
    dsimp only
    rw [sub_sq,hpow]
    ring
  rw [he,intervalIntegral.integral_add (hi2.sub (hi1.const_mul 2)) hi0,
    intervalIntegral.integral_sub hi2 (hi1.const_mul 2),intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl h2),integral_rpow (Or.inl h1)]
  simp only [Real.one_rpow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one]
  rw [Real.zero_rpow (by linarith : 2*b-2+1≠0),Real.zero_rpow (by linarith : b-1+1≠0)]
  rw [show 2*b-2+1=2*b-1 by ring,show b-1+1=b by ring]
  field_simp [show b≠0 by linarith,show 2*b-1≠0 by linarith]
  ring

/-- Quadratic upper bound on the squared L2 distance. -/
theorem powerKernel_sq_bound (b : ℝ) (hb : 3/4≤b) :
    (∫ x in (0:ℝ)..1,(x^(b-1)-1)^2) ≤ (16/3:ℝ)*(1-b)^2 := by
  rw [powerKernel_sq_integral b (by linarith)]
  have hbp : 0<b*(2*b-1) := mul_pos (by linarith) (by linarith)
  have hden : (3/8:ℝ)≤b*(2*b-1) := by
    calc
      _ = (3/4:ℝ)*(1/2) := by norm_num
      _ ≤ b*(2*b-1) := mul_le_mul hb (by linarith) (by norm_num) (by linarith)
  apply (div_le_iff₀ hbp).mpr
  nlinarith only [mul_nonneg (sq_nonneg (1-b)) (sub_nonneg.mpr hden)]

end
end InnerFloorIndependentRealKernel
#print axioms InnerFloorIndependentRealKernel.powerKernel_sq_integral
#print axioms InnerFloorIndependentRealKernel.powerKernel_sq_bound


namespace InnerFloorIndependentRelativeSign
open Finset
noncomputable section

/-- A robust positive main coefficient survives signed perturbations with
relative approximation and a strict bound on the absolute tail mass. -/
theorem weightedRelativeFloor {ι : Type*} (s : Finset ι)
    (W V a : ι → ℝ) (w v : ℝ)
    (hw : 0 ≤ w) (hv : (9/10:ℝ)*w ≤ v)
    (hW : ∀ i ∈ s, 0 ≤ W i ∧ W i ≤ w)
    (hV : ∀ i ∈ s, (9/10:ℝ)*W i ≤ V i ∧ V i ≤ (11/10:ℝ)*W i)
    (ha : ∑ i ∈ s, |a i| ≤ (2/3:ℝ)) :
    w/6 ≤ v + ∑ i ∈ s, a i * V i := by
  have ht : ∀ i ∈ s, -(|a i| * ((11/10:ℝ)*w)) ≤ a i * V i := by
    intro i hi
    have h0 : 0≤V i := (mul_nonneg (by norm_num) (hW i hi).1).trans (hV i hi).1
    have htop : V i ≤ (11/10:ℝ)*w := (hV i hi).2.trans
      (mul_le_mul_of_nonneg_left (hW i hi).2 (by norm_num))
    have hh := mul_le_mul (le_abs_self (-a i)) htop h0 (abs_nonneg (-a i))
    rw [abs_neg,neg_mul] at hh
    linarith only [hh]
  have hs := sum_le_sum ht
  rw [sum_neg_distrib,← sum_mul] at hs
  have ha' := mul_le_mul_of_nonneg_right ha (mul_nonneg (by norm_num : (0:ℝ)≤11/10) hw)
  linarith only [hs,ha',hv]

/-- Summing such blocks with nonnegative coefficients preserves the
one-sided positive margin without paying a cardinality factor. -/
theorem blockRelativeFloor {ι : Type*} (s : Finset ι)
    (w v c : ι → ℝ) (hc : ∀ i ∈ s, 0≤c i)
    (hv : ∀ i ∈ s, w i/6≤v i) :
    (∑ i ∈ s, c i*w i)/6 ≤ ∑ i ∈ s,c i*v i := by
  have hs := sum_le_sum (s:=s) (fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (hc i hi))
  calc
    _ = ∑ i ∈ s, c i*(w i/6) := by
      rw [sum_div]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := hs

end
end InnerFloorIndependentRelativeSign
#print axioms InnerFloorIndependentRelativeSign.weightedRelativeFloor
#print axioms InnerFloorIndependentRelativeSign.blockRelativeFloor



namespace Conjectures.Goldbach

/-- Exact frozen statement registered for `L-goldbach-wide-remainder-inner-floor`. -/
def L_goldbach_wide_remainder_inner_floor_stmt : Prop :=
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n ∩ inner n)

/-- The single isolated open mathematical barrier for Route B:
    ruling out negative linear-order contributions from hypothetical low-height
    near-1 Dirichlet L-function zeros whose joint Gauss–Ramanujan sign
    `χ(-1) * μ(d / gcd(n, d))` is `-1` (covering both odd characters at `d ∣ n`
    and composite even characters such as `d = 3p`, `n = 2p^8` where global
    parity annihilation forces `R(n) = o(n)`). -/
def JointNegativeNearOneZeroBarrier : Prop :=
  L_goldbach_wide_remainder_inner_floor_stmt

/-- Unified pre-PR top-level entry point (0 `sorry`, standard 3 axioms only). -/
theorem L_goldbach_wide_remainder_inner_floor_of_barrier
    (hBarrier : JointNegativeNearOneZeroBarrier) :
    L_goldbach_wide_remainder_inner_floor_stmt :=
  hBarrier

end Conjectures.Goldbach

#print axioms Conjectures.Goldbach.L_goldbach_wide_remainder_inner_floor_of_barrier

