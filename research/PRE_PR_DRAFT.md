# [Pre-PR Draft — DO NOT SUBMIT WITHOUT USER REVIEW] `L-goldbach-wide-remainder-inner-floor` (Route B Unified Formalization)

- **Target Task**: `L-goldbach-wide-remainder-inner-floor`
- **Assigned Single File**: `lean/Conjectures/Goldbach/WideRemainderInnerFloor.lean`
- **File Size**: `183102` bytes (`178.8` KiB, well under the 2 MiB single-file limit)
- **Exact SHA256**: `ca6fd367b05cfce6784dab7da45e8858b6497c7cd9fc7e5c590847bf29c6d39c`
- **Total `#print axioms` Audits**: `59` (all `[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero GRH imports)
- **Official Claim Branch**: `goldbach/L-goldbach-wide-remainder-inner-floor/d95a156c` (kept clean & untouched until user review)
- **Pre-PR Verification Branch**: `pre-pr/L-goldbach-wide-remainder-inner-floor-route-b`

## Summary of Unconditionally Verified Results
1. **End-to-End Tapered Zero-Occurrence Residual (`InnerFloorOccurrence.denominatorResidualFloor`)**:
   - Integrates the accepted zero-density theorem `DyadicCellShortPrimeFloor` (`V1f0`), actual trapezoid taper $L^2$ bounds, real-part exponent preservation $N^{\operatorname{Re}\rho+\operatorname{Re}\sigma-1}$, high product-conductor saving $1/\sqrt{D}$, and small GCD ratio saving $\sqrt{\gcd(n,L)/L}$.
   - Unconditionally reduces the denominator-first zero-occurrence sum to the triple-gate residual $\mathcal{R}_3$ minus $2W^3 N/L^m$.
2. **Signed Bilinear Floor & Model–Bad Cross Vanishing (`InnerFloorRouteB`)**:
   - `signedBilinearCellFloor`: replaces the two-sided $L^2$ bottleneck with a one-sided signed lower bound retaining full sign on $b^2$ and $2Mb$.
   - `shiftedGauss_nonprincipal_eq_zero_of_dvd`: proves the model–bad cross Gauss sum vanishes identically whenever $q \mid n$ and $\psi \neq 1$.
   - `primitive_quadratic_gaussSum_sq` & `pair_parity_split`: partitions $\mathcal{R}_3$ into even real diagonal ($+q$), odd real diagonal ($-q$), and off-diagonal/non-real pairs.
3. **Even Positivity & Exact Odd-Zero Necessity/Sufficiency Thresholds (`InnerFloorRouteBThreshold`)**:
   - `evenRealDiag_contribution_nonneg`: proves even real diagonal packets are nonnegative ($\ge 0$).
   - `oddReal_logGap_violates_floor`: proves classical $1-\beta = c/\log q$ violates $-\varepsilon n$ at $n = q^k$ ($\varepsilon < e^{-2kc}$).
   - `oddReal_superLogGap_satisfies_floor`: proves $(1-\beta)\log n \ge \frac{1}{2}\log(q/(\varphi(q)\varepsilon))$ suffices.
4. **Unconditional Almost-All Even $n$ Closure (`InnerFloorRouteBAlmostAll`)**:
   - `familyHighGcd_card_le_real`: proves the Gate-3 exceptional set has cardinality $\le X \cdot M \sum_{d \in D} \tau(d)/d$, closing the almost-all even $n$ version unconditionally.

## Transparent Scope & Single Isolated Open Barrier
- **IMPORTANT**: This pre-PR file is **NOT** a complete unconditional proof of `L-goldbach-wide-remainder-inner-floor` and **must NOT** be submitted to `goldbach.py submit` as a completed proof while `OddNearOneZeroBarrier` remains a hypothesis.
- The single remaining open mathematical problem is isolated in `Conjectures.Goldbach.OddNearOneZeroBarrier`: ruling out negative contributions from hypothetical odd low-height near-1 zeros at $d \mid n$ (requiring a $q$-aspect super-logarithmic zero-free input beyond classical de la Vallée Poussin and Siegel bounds).
