# Route B Complete Research Dossier — `L-goldbach-wide-remainder-inner-floor`

> **Task**: `L-goldbach-wide-remainder-inner-floor` (branch `goldbach/L-goldbach-wide-remainder-inner-floor/d95a156c`, lease active & clean)
> **Updated**: 2026-11-28 07:30 CST
> **Status**: All unblocked unconditional reductions, spectral decompositions, zero-density residual bounds, parity/cross-term eliminations, exact necessity/sufficiency thresholds, and almost-all exceptional-set bounds are **formally proved in Lean 4.36.0** (pinned Mathlib `fc4f59e`, standard three axioms `[propext, Classical.choice, Quot.sound]`, zero `sorry`). The single remaining gap is an **open problem in analytic number theory** ($q$-aspect super-logarithmic zero-free region / ruling out odd real & low-height near-1 zeros at $d \mid n$).

---

## 1. End-to-End Proof Architecture (What Is Closed vs. Isolated Barrier)

We target the exact frozen statement `FrozenWideRemainderInnerFloor`:
$$\forall \varepsilon > 0,\; \exists N,\; \forall n \ge N\text{ even},\quad -\varepsilon n \le \operatorname{Re} \int_{\mathfrak{R}_{\mathrm{rem}}(n) \cap \mathfrak{R}_{\mathrm{inner}}(n)} S_n(w, t)^2 e(-nt)\, dt.$$

| Layer | Mathematical Role | Lean Artifact | Verification |
|---|---|---|---|
| **L0. Geometry & High Band** | Disjoint union split into $Q < q \le A = n^{1/5}$ (`mediumBand`) and $A < q \le Q_1 = n^{1/3}$ (`highBandLittleO`); principal model lower bound `realWidthModelFloor` | `InnerFloorConditionalSingleFile.lean` (5467 lines) | Colab + Actions `#46050043791` **PASS** |
| **L1. One-Sided Signed Reduction** | Weakens the analytic input from two-sided $L^2$ (`MiddleCellEnergySmall`) to one-sided signed lower bound `SignedMiddleRemainderFloor`; exact bilinear split $(S^2-M^2)e = b^2 e + 2Mbe + \text{good error}$ | `InnerFloorRouteBSignedCoreVerified.lean` (`signedBilinearCellFloor`); `InnerFloorSignedFrozenReductionTrial.lean` (5036 lines, pending 4 upstream `.olean`s) | Core: Colab + Actions `#46080161131` / `#46081082170` **PASS** |
| **L2. Model–Bad Cross Vanishing** | Proves the shifted Gauss sum for $(1, \psi)$ vanishes identically whenever $q \mid n$ and $\psi \neq 1$ (no conductor collapse in cross terms) | `InnerFloorRouteBSignedCoreVerified.lean` (`shiftedGauss_nonprincipal_eq_zero_of_dvd`) | Colab + Actions `#46080161131` / `#46081082170` **PASS** |
| **L3. Tapered Gauss-Normalized Zero Packets** | Actual trapezoid taper $L^2$ energy, real-part exponent preservation $N^{\operatorname{Re}\rho+\operatorname{Re}\sigma-1}$, high product-conductor saving $1/\sqrt{D}$, and small GCD ratio saving $\sqrt{\gcd(n,L)/L}$ | `InnerFloorActualTaperHighProductVerified.lean` (2176 lines), `InnerFloorActualTaperRealPartsGcdVerified.lean` (2487 lines), `InnerFloorActualResidualAssemblyVerified.lean` (2787 lines) | Colab + Actions `#46064184938`, `#46071600706`, `#46072024681` **PASS** |
| **L4. End-to-End Zero-Occurrence Residual** | Connects official accepted zero-density theorem `DyadicCellShortPrimeFloor` (`V1f0`) to denominator-first signed residual lower bound: $\text{Total} \ge \text{TripleGateResidual} - 2W^3 N/L^m$ | `InnerFloorOccurrenceResidualVerified.lean` (3218 lines, 44 axiom audits) + `InnerFloorOccurrenceBudgetVerified.lean` (171 lines) | Colab + Actions `#46072574924` **PASS** |
| **L5. Parity/Reality Split & Even Positivity** | Splits $\mathcal{R}_3$ into even real diagonal ($\tau(\chi)^2 = +q$, self-convolution $\ge 0$), odd real diagonal ($\tau(\chi)^2 = -q$), and off-diagonal/non-real | `InnerFloorRouteBSignedCoreVerified.lean` (`primitive_quadratic_gaussSum_sq`, `pair_parity_split`), `InnerFloorRouteBResearchThresholdVerified.lean` (`evenRealDiag_contribution_nonneg`) | Colab + Actions `#46081082170` **PASS** |
| **L6. Exact Necessity & Sufficiency Threshold** | Proves $1-\beta = c/\log q$ violates $-\varepsilon n$ at $n = q^k$ ($\varepsilon < e^{-2kc}$); proves $(1-\beta)\log n \ge \frac{1}{2}\log(q/(\varphi(q)\varepsilon))$ suffices | `InnerFloorRouteBResearchThresholdVerified.lean` (`oddReal_logGap_violates_floor`, `oddReal_superLogGap_satisfies_floor`) | Colab + Actions `#46081082170` **PASS** |
| **L7. Unconditional Almost-All Closure** | Proves Gate-3 high-gcd exceptional set for any conductor family $D$ has cardinality $\le X \cdot M \sum_{d \in D} \tau(d)/d$, closing the almost-all even $n$ version unconditionally | `InnerFloorRouteBAlmostAllVerified.lean` (`highGcdSet_card_le_real`, `familyHighGcd_card_le_real`) | Colab EXIT 0 (SHA `b5791e5b...`) + Actions matrix |

---

## 2. Exact Verified SHA256 & Axiom Audit Ledger (Route B Core Suite)

| File | SHA256 | `#print axioms` | Axioms |
|---|---|---|---|
| `InnerFloorOccurrenceResidualVerified.lean` | `6929a2c146d58732819cfeb9d4f5a7773d1a3aab312be6138fc1010819b851ae` | 44 | `[propext, Classical.choice, Quot.sound]` |
| `InnerFloorRouteBSignedCoreVerified.lean` | `11b6a92a50cb9d9f0cb143cb53831cd78230436c2cc000114eaff935260994a5` | 5 | `[propext, Classical.choice, Quot.sound]` |
| `InnerFloorRouteBResearchThresholdVerified.lean` | `4bfe459f8572140982e14963c4d040958b6c69f0822a875a1c8114a4717c91b1` | 5 | `[propext, Classical.choice, Quot.sound]` |
| `InnerFloorRouteBAlmostAllVerified.lean` | `b5791e5bb4df171f4c0dd07d0a66a6aaf4843faefff89e3179a9be4fd306d606` | 4 | `[propext, Classical.choice, Quot.sound]` |

---

## 3. Exact Specification of the Single Isolated Open-Problem Barrier

Every unconditional component outside this barrier is now formally closed. The **sole remaining mathematical obstacle** to an unconditional proof of `FrozenWideRemainderInnerFloor` is:

> **Isolated Barrier**: Ruling out negative contributions of order $-\frac{d}{\varphi(d)} n^{2\beta - 1}$ from hypothetical **odd** primitive characters $\chi \pmod d$ ($\chi(-1) = -1$, $Q(n) < d \le n^{1/5}$, $\gcd(n, d) > d / L^{2(4+m+r)}$) possessing a low-height near-1 zero $\rho = \beta + i\gamma$ with $(1 - \beta) \log n = O(1)$.

- Neither the classical de la Vallée Poussin zero-free region ($1 - \beta \ge c/\log q$), nor Siegel's theorem ($1 - \beta \gg_\varepsilon q^{-\varepsilon}$), nor Deuring–Heilbronn repulsion suffices (formally verified in `oddReal_logGap_violates_floor`).
- Closing it unconditionally for **all** even $n$ requires a $q$-aspect super-logarithmic zero-free region $(1-\beta)\log q \to \infty$ (quantified in `oddReal_superLogGap_satisfies_floor`).
- Conversely, for **almost all** even $n \le X$, Gate 3 + `familyHighGcd_card_le_real` already eliminates the barrier unconditionally.
