module

public import QR.Alpha
public import QR.Basic
public import QR.Bottle
public import QR.Gravity
public import QR.Helium
public import QR.J4
public import QR.Jacobi
public import QR.Markov
public import QR.MassRatio
public import QR.Polarizability
public import QR.Ports
public import QR.Spin
public import QR.Stencil
public import QR.Thermo
public import QR.Transport

set_option linter.style.header false

/-!
# Deductive ledger

The names in this comment are theorems in this package. The TeX label is the name
the manuscript uses. These identities are the algebra of the formulas in the revised
manuscript. They do not certify numerical agreement with CODATA, and they do not
select the vacuum or the hydrogen representation from a list of candidates.
Numerical CODATA residuals, the two-photon decimal, the Bethe logarithm,
cubic-pocket eigenvalues, and the evaluated helium correlation `-0.11974 Ry`
are not part of the proof kernel.

## Proved

* `thm:story_bright_dark`, `eq:record_prob`, mean resolution time `τ/p`: `Ports`.
* `prop:bell_chsh`, `eq:bell_chsh_bound`: `chsh_tsirelson`. Singlet reduced state `I/2`.
* `thm:variable_stretch`, `eq:variable_stretch_transport`, `eq:adiabatic_redshift`: `Transport`.
* `thm:extended_markovian`, `eq:unitary_contract`, `eq:readiness_bound`, pulse windows: `Markov`.
* `eq:relational_first_law`, `eq:atomic_pressure_balance`: `Thermo` and `pressure_zero_at_rydberg`.
* `thm:transverse_photon`, `eq:mainM`, `eq:mainWalsh`, `C_{ℓ=3}` kernel, shell `n²`: `J4`.
* `prop:840_stencil`, `eq:840_weights`, port counts `120` and `840`: `Stencil`.
* `T21` port formula: `Alpha`. `N_cells = 15`, `N_cell = 16`, `N_tot = 137`,
  `N_dyn = 122`, and `Σ_dyn = π²/122`. The Dirichlet mode `√2 sin(π s)` is normalized,
  vanishes at the endpoints, satisfies `-ψ'' = π² ψ`, and has `ℰ₁ = π²/2` both as
  `½ ∫ (ψ')²` and as `½ ∫ ψ (-ψ'')`. One loop is `137 + π²/274`. Two loops are the
  closed impedance `π² / (2 (137 + π²/122))`, equal to
  `π²/(2·137) - π⁴/(2·137²·122)` plus a positive remainder, so the truncation lies
  strictly below the closed form. CODATA residuals and the printed `ppb` / `σ`
  comparisons are not theorems.
* `thm:discrete_graph_to_jacobi`, `thm:rydberg_closure`, `eq:discrete_virial`: `Jacobi`.
* `thm:reduced_mass_recoil`: isotope shift `1/(12π⁵+1)` at `m_p/m_e = 6π⁵`, the fraction
  boxed in the manuscript. The printed decimal is not a theorem.
* Dressed mass `6π⁵ + (24/25) δN_imp`: `MassRatio`, using `‖M_LF‖_F² = 12` and
  `2·12 + 1 = 25` from `J4`. One loop substitutes `π²/274`; two loops substitute
  `π² / (2 (137 + π²/122))`. The CODATA comparison is not a theorem.
* `thm:no_free_electron`: for `ε > 0` the `K₁` coefficient does not vanish.
  The Casimir from `eq:secular_D` is `-4 ζ² ε`, as in the manuscript.
* `thm:sommerfeld_dirac`: the boxed spectrum. Zero leakage
  `ζ = 2 √(m²c⁴ - E²)/(ℏ c)` together with `(ζ/2) ν = Zα E/(ℏ c)` solves to it.
* `thm:su2_spin_fine`, `eq:su2_holonomy`, `eq:lande_gJ`, `eq:bezginov_hfs`: `Basic`, `Spin`.
  The `2S` and `2P` pieces are `3/32` and `1/96` of `Δν(1S)`, and they sum to `5/48`.
* `thm:schwinger_zeeman`: `∫₀¹ (1-u) du = 1/2`, and `a_e = α/(2π)` once the form factor
  is supplied as a hypothesis.
* `thm:diagonal_resolvent`, `eq:polarizability_1s`: `9/2`. The manuscript integrand is `x⁴ e^{-x}`.
* Stark product `3√3 · 1/√3 = 3` and Lamb ratio `(2/n)³`.
* Helium: density `(1/2) ∫ x² e^{-x} = 1`, bracket `5/16`, `E(Z=2) = -729/128`,
  screening `25/128 = 2(5/16)²`, and the expansion `-2(Z - 5/16)² = -2Z² + (5/4)Z - 25/128`.
  Lithium's inner scale is `(43/16) g`. The normal mass shift is the virial
  `⟨p₁² + p₂²⟩ = -2 m E`. For the specific mass shift, `R₀' = -R₀/2`,
  `x u₀ = √3 f₀⁽¹⁾`, the `j = 0` Sturmian weight is `1`, and the `L²` overlap is `√3`.
  Any integrable weight against `f₀⁽¹⁾` scales that overlap by `√3`.
  The gradient coefficient `-√3/4` is the manuscript's `L = 0` contraction of these
  identities; the Condon–Shortley coupling gives `+√3/4`. Appendix H writes
  `c = -2 ℒ⁻¹ v` and Section 7 writes `c = -ℒ⁻¹ v`. The verifier uses the appendix
  factor. The correlation sum `-0.11974 Ry` is not a theorem.
* `thm:vacuum_and_mass` algebraic core: oscillator identity, `eq:RS_s` floor, moment Cauchy,
  window constants `ν = ℏ²/(64 μ H*)`, affine second difference of `c₂(n)`.
  The drift inequality `c ≤ E + b √E` inverts to `(b²/4) (√(1 + 4c/b²) - 1)²`.
  With `b = √(ℏΩ/2)` and `c = ℏ|α|⟨|s|⟩ / (4 √(2μM))`, that floor is
  `(ℏΩ/8) (√(1 + 2λ) - 1)²`, the boxed pinch cost, with strong-pinch slope
  `ℏ|α| / (4 √(2μM))`. Replacing `2λ` by `λ` weakens the floor.
  The operator diamagnetic inequality remains an interface.
* PPN: `g₀₀ = -(1-φ)/(1+φ)` with remainder `2φ³/(1+φ)`, `g_ij = (1+φ)²`, horizon
  `2GM/c²`, collar cancellation `(h_b/Δℓ)/h_b = 1/Δℓ`.
* Refractive index: `n(0) = 1` and `n'(0) = 2`. The logarithmic slope at the origin is
  `-1`, and `n'(0) g(0) + n(0) g'(0) = 3`, so the quadratic Taylor coefficient is `3/2`,
  matching `1 + 2φ + (3/2)φ²`.
* DtN comparison jets `sinh x · (1 + x²/3) - x cosh x` and `sinh x · (1 - x²/6) - x`
  vanish at the origin. The coefficient `1/3` and `-1/6` are the ones that make those
  jets the order-two contact; higher derivatives of the jets are not expanded here.
* Chiral vertex `P₋ σ₂ P₊` and the vanishing of `P₊ σ₂ P₊`.

## Named interfaces, not proved here

* Favard uniqueness, the continuum identification of the discrete Jacobi pencil with `-g/r`.
* Gleason uniqueness for the `L²` story measure. Finite isometries `Sᵀ S = I` are proved.
* The operator diamagnetic inequality. The scalar floor `rs_floor` is proved.
* The spectral theorem for the continuum magnetic form. Finite moment comparison is proved.
* The one-loop form-factor reduction in `schwinger_anomaly` is a hypothesis.

## Left in C4

* High-`Q²` running of `α(Q²)` and the continuum Ward–Takahashi identity at
  arbitrary momentum transfer.
* The nonlinear Duhamel cone and the full spin-2 Einstein system.
-/
