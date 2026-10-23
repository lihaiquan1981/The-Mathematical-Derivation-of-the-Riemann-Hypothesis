module

/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Support

@[expose] public section

open Complex Filter

/-!
The statements Palomar compares. Each named theorem is proved in `Solution`
under exactly the hypotheses written on its signature. Those hypotheses are
not discharged here. None of these statements is the 1859 German sentence.

Labels such as "Theorem 9.3A" or "Lemma 9.4" are the author's own numbering and
serve only as names.
-/

/-- Index action of `A : s ↦ 1 - conj s` on `orbit`: swaps 0 ↔ 1 and 2 ↔ 3. -/
def iA : Fin 4 → Fin 4 := ![1, 0, 3, 2]
/-- Index action of `B : s ↦ conj s` on `orbit`: swaps 0 ↔ 2 and 1 ↔ 3. -/
def iB : Fin 4 → Fin 4 := ![2, 3, 0, 1]
/-- Action of `A` on a plane vector: the first coordinate changes sign. -/
def JA (u : ℝ × ℝ) : ℝ × ℝ := (-u.1, u.2)
/-- Action of `B` on a plane vector: the second coordinate changes sign. -/
def JB (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)
/-- Euclidean inner product on `ℝ × ℝ`. -/
def dot (w u : ℝ × ℝ) : ℝ := w.1 * u.1 + w.2 * u.2
/-- Euclidean norm on `ℝ × ℝ`. Mathlib's norm on a product is the max norm. -/
noncomputable def nrm2 (u : ℝ × ℝ) : ℝ := Real.sqrt (u.1 ^ 2 + u.2 ^ 2)

/-- Coupling quadratic form of the double-reflection kernel on a four-point
vector field `w`: each point is paired with its `A`-image through `JA` and with
its `B`-image through `JB`, with coupling constant `C`. -/
noncomputable def Kquad (C : ℝ) (w : Fin 4 → ℝ × ℝ) : ℝ :=
  (C / 4) * ∑ i : Fin 4, (dot (w i) (JA (w (iA i))) + dot (w i) (JB (w (iB i))))

/-- Imaginary part of `f` at the point `x + y i`, read as a real function of `(x, y)`. -/
def vim (f : ℂ → ℂ) (u : ℝ × ℝ) : ℝ := (f (↑u.1 + ↑u.2 * I)).im

/-- Reflection in the critical line `Re s = 1/2`, in coordinates. -/
def reflA (u : ℝ × ℝ) : ℝ × ℝ := (1 - u.1, u.2)
/-- Reflection in the real axis, in coordinates. -/
def reflB (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)

/-- Gradient of `vim f` at `u`, by partial derivatives in `x` and `y`. -/
noncomputable def nablaV (f : ℂ → ℂ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun x => vim f (x, u.2)) u.1, deriv (fun y => vim f (u.1, y)) u.2)

/-- The four-point orbit of `(σ, t)` under the two reflections. -/
def orbit (σ t : ℝ) : Fin 4 → ℝ × ℝ := ![(σ, t), (1 - σ, t), (σ, -t), (1 - σ, -t)]

/-- The gradient field of `vim f` sampled on the orbit of `(σ, γ)`. -/
noncomputable def orbitGrad (f : ℂ → ℂ) (σ γ : ℝ) : Fin 4 → ℝ × ℝ :=
  fun i => nablaV f (orbit σ γ i)

/-- The orbit as complex numbers `ρ, 1 - conj ρ, conj ρ, 1 - ρ` with `ρ = σ + i t`. -/
noncomputable def orbitC (σ t : ℝ) : Fin 4 → ℂ :=
  ![↑σ + I * ↑t, 1 - star (↑σ + I * ↑t), star (↑σ + I * ↑t), 1 - (↑σ + I * ↑t)]

/-- Riemann's `ξ(s) = s (s - 1) / 2 · π^(-s/2) Γ(s/2) ζ(s)`, written with Mathlib's
`completedRiemannZeta`. Its values at `s = 0, 1` are artefacts of Mathlib's
junk convention, so the assemblies only use it off `{0, 1}`. -/
noncomputable def xiFn (s : ℂ) : ℂ := (s * (s - 1) / 2) * completedRiemannZeta s

/-- Theorem 9.3A. An entire `f` with `f s = f (1 - s)` and Schwarz reflection
has a unique representation `f s = g ((s - 1/2)^2)` with `g` entire and real on
the real axis. -/
theorem theorem_9_3A
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f s = f (1 - s))
    (h_conj : ∀ s, f (star s) = star (f s)) :
    (∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ t : ℝ, (g ↑t).im = 0) ∧
      (∀ s : ℂ, f s = g ((s - 1/2)^2))) ∧
    (∀ g1 g2 : ℂ → ℂ, (∀ s : ℂ, f s = g1 ((s - 1/2)^2)) →
      (∀ s : ℂ, f s = g2 ((s - 1/2)^2)) → g1 = g2) := by
  sorry

/-- Integer arithmetic certificate: for `C > ε > 0`, `-2C + 2ε < 0`,
`2C + 2ε > 0`, `2ε > 0`, and `2C > 0`. -/
theorem mother_equation_core_certificate (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    (-2 * C + 2 * ε < 0) ∧ (2 * C + 2 * ε > 0 ∧ 2 * ε > 0) ∧ (2 * C > 0) := by
  sorry

/-- Lemma 9.4. For entire `f` with both reflections, `Im f` is odd under each
reflection, vanishes on the critical line and on the real axis, and has nonzero
gradient wherever `f′ ≠ 0`. -/
theorem lemma_9_4 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s)) :
    (∀ u : ℝ × ℝ, vim f (reflA u) = -vim f u) ∧
    (∀ u : ℝ × ℝ, vim f (reflB u) = -vim f u) ∧
    (∀ y : ℝ, vim f (1 / 2, y) = 0) ∧
    (∀ x : ℝ, vim f (x, 0) = 0) ∧
    (∀ σ γ : ℝ, deriv f (↑σ + ↑γ * I) ≠ 0 → nablaV f (σ, γ) ≠ 0) := by
  sorry

/-- Lemma 9.5C, part (ii): on a nonzero χAB-type configuration
(`w ∘ iA = JB ∘ w`, `w ∘ iB = JA ∘ w`) the coupling form is strictly negative. -/
theorem Kquad_chiAB_neg (C : ℝ) (w : Fin 4 → ℝ × ℝ) (hC : 0 < C)
    (hA : ∀ i, w (iA i) = JB (w i)) (hB : ∀ i, w (iB i) = JA (w i))
    (hne : ∃ i : Fin 4, w i ≠ 0) :
    Kquad C w < 0 := by
  sorry

/-- Theorem 9.5, simple-zero form. A zero `σ + i t` with `σ ≠ 1/2`, `t ≠ 0` of an
entire doubly reflected `f` contradicts the unitarity hypothesis `hunit`, which
asks the coupling form to be positive on the orbit gradient of such a zero. -/
theorem theorem_9_5_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → deriv f (↑σ + I * ↑t) ≠ 0)
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t))
    {σ t : ℝ} (hz : f (↑σ + I * ↑t) = 0) (hσ : σ ≠ 1 / 2) (ht : t ≠ 0) :
    False := by
  sorry

/-- Theorem 10, simple-zero form: under `hsimple` and `hunit`, every zero of `f`
off the critical line is real. -/
theorem theorem_10_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → deriv f (↑σ + I * ↑t) ≠ 0)
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t)) :
    ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t = 0 := by
  sorry

/-- Lemma 11.3. Given `hζ`, `ξ` is real and positive at real points other than 0, 1. -/
theorem lemma_11_3
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (0 : ℝ) < (xiFn (x : ℂ)).re ∧ (xiFn (x : ℂ)).im = 0 := by
  sorry

/-- If `(s - 1/2)^2` is a negative real number, then `Re s = 1/2`. -/
theorem critical_line_lock {s : ℂ} {w : ℝ}
    (hw : (s - 1 / 2) ^ 2 = (w : ℂ)) (hwneg : w < 0) :
    s.re = 1 / 2 := by
  sorry

/-- General assembly, simple-zero form: under `hsimple` and `hunit`, every zero
of `f` is on the critical line or real. -/
theorem RH_general (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → deriv f (↑σ + I * ↑t) ≠ 0)
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t))
    {σ t : ℝ} (hz : f (↑σ + I * ↑t) = 0) :
    σ = 1 / 2 ∨ t = 0 := by
  sorry

/-- ξ assembly, simple-zero form. For an entire `g` equal to `xiFn` off `{0, 1}`,
under `hunit`, `hζ`, and simplicity of zeros, every zero other than 0, 1 has
real part 1/2. -/
theorem RH_xi (C : ℝ) (hC : 0 < C)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hunit : ∀ σ t : ℝ, g (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad g σ t))
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    (hg_simple : ∀ σ t : ℝ, g (↑σ + I * ↑t) = 0 → deriv g (↑σ + I * ↑t) ≠ 0)
    {s : ℂ} (hz : g s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s.re = 1 / 2 := by
  sorry

/-- The zero set of `g` in `RH_xi` lies in the critical line together with `{0, 1}`. -/
theorem RH_xi_zeros (C : ℝ) (hC : 0 < C)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hunit : ∀ σ t : ℝ, g (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad g σ t))
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    (hg_simple : ∀ σ t : ℝ, g (↑σ + I * ↑t) = 0 → deriv g (↑σ + I * ↑t) ≠ 0)
    {s : ℂ} (hz : g s = 0) :
    s.re = 1 / 2 ∨ s = 0 ∨ s = 1 := by
  sorry

/-- Theorem 9.5 for zeros of any multiplicity. `E m` is the order-`m` jet energy
form. `hE_pos` is the unitarity hypothesis on the jet configuration of an
off-line nonreal zero; `hE_neg` asks `E m` to be negative on every nonzero jet
with the χAB pairing. The two together exclude such a zero. -/
theorem theorem_9_5_multiplicity (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (f : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, f (↑σ + I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m f (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hne : ∃ s, f s ≠ 0)
    {σ t : ℝ} (hz : f (↑σ + I * ↑t) = 0) (hσ : σ ≠ 1 / 2) (ht : t ≠ 0) :
    False := by
  sorry

/-- ξ assembly for zeros of any multiplicity. The simplicity hypothesis of
`RH_xi` is removed; `hE_pos`, `hE_neg`, and `hζ` stay on the signature. -/
theorem RH_xi_any_multiplicity (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (g : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, g (↑σ + I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m g (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg : Differentiable ℂ g)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    {s : ℂ} (hz : g s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s.re = 1 / 2 := by
  sorry

/-- Section 5A.8 under the spectral reading `hSpec : Set.range α = Z`: real roots,
real spectrum, symmetry, a unitary group, and real energies are equivalent.
This does not prove that the roots are real. -/
theorem five_eight_equiv {ι : Type*} (α : ι → ℂ) (Z : Set ℂ) (hSpec : Set.range α = Z) :
    Z ⊆ {z : ℂ | z.im = 0} ↔
      Set.range α ⊆ {z : ℂ | z.im = 0} ∧
      (∀ i, ∀ x y : ℂ, star (α i * x) * y = star x * (α i * y)) ∧
      ((∀ i, ∀ τ : ℝ, ‖exp (I * (τ : ℂ) * α i)‖ = 1) ∧
        ∀ i, Tendsto (fun τ : ℝ => exp (I * (τ : ℂ) * α i)) (nhds 0) (nhds 1)) ∧
      (∀ i, (α i).im = 0) := by
  sorry

/-- Theorem 10 for zeros of any multiplicity: under `hE_pos` and `hE_neg`, every
zero of `f` off the critical line is real. -/
theorem theorem_10_any_multiplicity (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (f : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, f (↑σ + I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m f (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hne : ∃ s, f s ≠ 0) :
    ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t = 0 := by
  sorry

/-- General assembly for zeros of any multiplicity: under `hE_pos` and `hE_neg`,
every zero of `f` is on the critical line or real. -/
theorem RH_general_any_multiplicity (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (f : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, f (↑σ + I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m f (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hne : ∃ s, f s ≠ 0)
    {σ t : ℝ} (hz : f (↑σ + I * ↑t) = 0) :
    σ = 1 / 2 ∨ t = 0 := by
  sorry

/-- The zero set of `g` in `RH_xi_any_multiplicity` lies in the critical line together with `{0, 1}`. -/
theorem RH_xi_zeros_any_multiplicity (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (g : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, g (↑σ + I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m g (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg : Differentiable ℂ g)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    {s : ℂ} (hz : g s = 0) :
    s.re = 1 / 2 ∨ s = 0 ∨ s = 1 := by
  sorry

/-- Taylor remainder for Lemma 9.5C. For a compactly supported `C²` field `Φ` with
bounded second derivative (`hBd`) and a zero `z0`, the first-order expansion at
`z0` has a remainder bounded by `M · ‖u‖²`. -/
theorem taylor_remainder_C2 {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    (hcs : HasCompactSupport Φ)
    (hBd : ∃ B, 0 ≤ B ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ Φ) z‖ ≤ B)
    (z0 : ℝ × ℝ) (hΦ0 : Φ z0 = 0) :
    ∃ M, 0 ≤ M ∧ ∀ u, |Φ (z0 + u) - (fderiv ℝ Φ z0) u| ≤ M * (nrm2 u) ^ 2 := by
  sorry

end
