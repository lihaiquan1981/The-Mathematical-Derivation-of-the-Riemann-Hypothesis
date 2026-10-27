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
The statements Palomar compares. Labels such as "Lemma 9.4" are the author's own numbering.
-/

def iA : Fin 4 → Fin 4 := ![1, 0, 3, 2]
def iB : Fin 4 → Fin 4 := ![2, 3, 0, 1]
def JA (u : ℝ × ℝ) : ℝ × ℝ := (-u.1, u.2)
def JB (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)
def dot (w u : ℝ × ℝ) : ℝ := w.1 * u.1 + w.2 * u.2
noncomputable def nrm2 (u : ℝ × ℝ) : ℝ := Real.sqrt (u.1 ^ 2 + u.2 ^ 2)

noncomputable def Kquad (C : ℝ) (w : Fin 4 → ℝ × ℝ) : ℝ :=
  (C / 4) * ∑ i : Fin 4, (dot (w i) (JA (w (iA i))) + dot (w i) (JB (w (iB i))))

def vim (f : ℂ → ℂ) (u : ℝ × ℝ) : ℝ := (f (↑u.1 + ↑u.2 * I)).im

def reflA (u : ℝ × ℝ) : ℝ × ℝ := (1 - u.1, u.2)
def reflB (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)

noncomputable def nablaV (f : ℂ → ℂ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun x => vim f (x, u.2)) u.1, deriv (fun y => vim f (u.1, y)) u.2)

def orbit (σ t : ℝ) : Fin 4 → ℝ × ℝ := ![(σ, t), (1 - σ, t), (σ, -t), (1 - σ, -t)]

noncomputable def orbitGrad (f : ℂ → ℂ) (σ γ : ℝ) : Fin 4 → ℝ × ℝ :=
  fun i => nablaV f (orbit σ γ i)

noncomputable def orbitC (σ t : ℝ) : Fin 4 → ℂ :=
  ![↑σ + I * ↑t, 1 - star (↑σ + I * ↑t), star (↑σ + I * ↑t), 1 - (↑σ + I * ↑t)]

noncomputable def xiFn (s : ℂ) : ℂ := (s * (s - 1) / 2) * completedRiemannZeta s

/-- Theorem 9.3A: the even reduction. -/
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

/-- An integer sign certificate. -/
theorem mother_equation_core_certificate (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    (-2 * C + 2 * ε < 0) ∧ (2 * C + 2 * ε > 0 ∧ 2 * ε > 0) ∧ (2 * C > 0) := by
  sorry

/-- Lemma 9.4: reflection laws of Im f. -/
theorem lemma_9_4 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s)) :
    (∀ u : ℝ × ℝ, vim f (reflA u) = -vim f u) ∧
    (∀ u : ℝ × ℝ, vim f (reflB u) = -vim f u) ∧
    (∀ y : ℝ, vim f (1 / 2, y) = 0) ∧
    (∀ x : ℝ, vim f (x, 0) = 0) ∧
    (∀ σ γ : ℝ, deriv f (↑σ + ↑γ * I) ≠ 0 → nablaV f (σ, γ) ≠ 0) := by
  sorry

/-- Lemma 9.5C (ii): the sign of Kquad on χAB configurations. -/
theorem Kquad_chiAB_neg (C : ℝ) (w : Fin 4 → ℝ × ℝ) (hC : 0 < C)
    (hA : ∀ i, w (iA i) = JB (w i)) (hB : ∀ i, w (iB i) = JA (w i))
    (hne : ∃ i : Fin 4, w i ≠ 0) :
    Kquad C w < 0 := by
  sorry

/-- Theorem 9.5, simple zeros. -/
theorem theorem_9_5_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → deriv f (↑σ + I * ↑t) ≠ 0)
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t))
    {σ t : ℝ} (hz : f (↑σ + I * ↑t) = 0) (hσ : σ ≠ 1 / 2) (ht : t ≠ 0) :
    False := by
  sorry

/-- Theorem 10, simple zeros. -/
theorem theorem_10_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → deriv f (↑σ + I * ↑t) ≠ 0)
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t)) :
    ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t = 0 := by
  sorry

/-- Lemma 11.3. -/
theorem lemma_11_3
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (0 : ℝ) < (xiFn (x : ℂ)).re ∧ (xiFn (x : ℂ)).im = 0 := by
  sorry

/-- The critical-line lock. -/
theorem critical_line_lock {s : ℂ} {w : ℝ}
    (hw : (s - 1 / 2) ^ 2 = (w : ℂ)) (hwneg : w < 0) :
    s.re = 1 / 2 := by
  sorry

/-- General assembly, simple zeros. -/
theorem RH_general (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → deriv f (↑σ + I * ↑t) ≠ 0)
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t))
    {σ t : ℝ} (hz : f (↑σ + I * ↑t) = 0) :
    σ = 1 / 2 ∨ t = 0 := by
  sorry

/-- Assembly, simple zeros. -/
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

/-- Zero set, simple zeros. -/
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

/-- Theorem 9.5, any multiplicity. -/
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

/-- Assembly, any multiplicity. -/
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

/-- Section 5A.8 equivalence. -/
theorem five_eight_equiv {ι : Type*} (α : ι → ℂ) (Z : Set ℂ) (hSpec : Set.range α = Z) :
    Z ⊆ {z : ℂ | z.im = 0} ↔
      Set.range α ⊆ {z : ℂ | z.im = 0} ∧
      (∀ i, ∀ x y : ℂ, star (α i * x) * y = star x * (α i * y)) ∧
      ((∀ i, ∀ τ : ℝ, ‖exp (I * (τ : ℂ) * α i)‖ = 1) ∧
        ∀ i, Tendsto (fun τ : ℝ => exp (I * (τ : ℂ) * α i)) (nhds 0) (nhds 1)) ∧
      (∀ i, (α i).im = 0) := by
  sorry

/-- Theorem 10, any multiplicity. -/
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

/-- General assembly, any multiplicity. -/
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

/-- Zero set, any multiplicity. -/
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

/-- Taylor remainder for Lemma 9.5C. -/
theorem taylor_remainder_C2 {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    (hcs : HasCompactSupport Φ)
    (hBd : ∃ B, 0 ≤ B ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ Φ) z‖ ≤ B)
    (z0 : ℝ × ℝ) (hΦ0 : Φ z0 = 0) :
    ∃ M, 0 ≤ M ∧ ∀ u, |Φ (z0 + u) - (fderiv ℝ Φ z0) u| ≤ M * (nrm2 u) ^ 2 := by
  sorry

end
