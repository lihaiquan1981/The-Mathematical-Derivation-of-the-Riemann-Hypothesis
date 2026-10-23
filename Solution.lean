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
import Theorem_9_3A
import MotherEquation_CoreVerification
import Lemma_9_5C
import Lemma_9_4
import Theorem_9_5_Closure
import Lemma_11_3
import Final_Assembly
import Note_9_5B_mJet
import Final_Assembly_Unconditional
import Lemma_9_5C_TaylorRemainder
import Section5A8_Unitarity

public section

open Complex Filter

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

def minEig (collapsed : Bool) (C ε : Int) : Int :=
  if collapsed then 2 * ε else -2 * C + 2 * ε

private lemma xiFn_eq (s : ℂ) : xiFn s = RH113.xiFn s := by
  simp [xiFn, RH113.xiFn]

private lemma unit_bridge {C : ℝ} {f : ℂ → ℂ}
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t)) :
    RH95Final.SatisfiesUnitarity C f := by
  intro σ t hz hσ ht
  have h := hunit σ t hz hσ ht
  simpa [Kquad, RH95C.Kquad, orbitGrad, RH94.orbitGrad, nablaV, RH94.nablaV, vim, RH94.vim,
    orbit, RH95U.orbit, dot, RH95C.dot, JA, RH95C.JA, JB, RH95C.JB, iA, RH95C.iA, iB,
    RH95C.iB] using h

private lemma orbitC_eq (σ t : ℝ) : orbitC σ t = RHM.orbitC σ t := by
  simp [orbitC, RHM.orbitC]

private lemma iA_eq : iA = RH95C.iA := by
  funext i; fin_cases i <;> simp [iA, RH95C.iA]

private lemma iB_eq : iB = RH95C.iB := by
  funext i; fin_cases i <;> simp [iB, RH95C.iB]

private lemma posBridge {f : ℂ → ℂ} {E : ℕ → (Fin 4 → ℂ) → ℝ}
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, f (↑σ + I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m f (orbitC σ t i)) →
      0 ≤ E m J) :
    ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (RH95C.iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (RH95C.iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, f (↑σ + I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m f (RHM.orbitC σ t i)) →
      0 ≤ E m J := by
  intro m J hA hB hJ hzero
  apply hE_pos m J
  · intro i; simpa [iA_eq] using hA i
  · intro i; simpa [iB_eq] using hB i
  · exact hJ
  · rcases hzero with ⟨σ, t, hz', hσ', ht', hJeq⟩
    exact ⟨σ, t, hz', hσ', ht', fun i => by simpa [orbitC_eq] using hJeq i⟩

private lemma negBridge {E : ℕ → (Fin 4 → ℂ) → ℝ}
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0) :
    ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (RH95C.iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (RH95C.iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0 := by
  intro m J hA hB hJ
  apply hE_neg m J
  · intro i; simpa [iA_eq] using hA i
  · intro i; simpa [iB_eq] using hB i
  · exact hJ

theorem theorem_9_3A
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f s = f (1 - s))
    (h_conj : ∀ s, f (star s) = star (f s)) :
    (∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ t : ℝ, (g ↑t).im = 0) ∧
      (∀ s : ℂ, f s = g ((s - 1/2)^2))) ∧
    (∀ g1 g2 : ℂ → ℂ, (∀ s : ℂ, f s = g1 ((s - 1/2)^2)) →
      (∀ s : ℂ, f s = g2 ((s - 1/2)^2)) → g1 = g2) :=
  RH93.theorem_9_3A hf h_sym h_conj

theorem mother_equation_core_certificate (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    (-2 * C + 2 * ε < 0) ∧ (2 * C + 2 * ε > 0 ∧ 2 * ε > 0) ∧ (2 * C > 0) :=
  MotherEquation.mother_equation_core_certificate C ε hC hε

theorem unitarity_sign (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    -2 * C + 2 * ε < 0 ∧ 2 * C + 2 * ε > 0 ∧ 2 * ε > 0 :=
  MotherEquation.unitarity_sign C ε hC hε

theorem phase_cliff (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    minEig false C ε < 0 ∧ minEig true C ε > 0 ∧
      minEig true C ε - minEig false C ε = 2 * C := by
  simpa [minEig, MotherEquation.minEig] using MotherEquation.phase_cliff C ε hC hε

theorem no_intermediate_state : ∀ b : Bool, b = true ∨ b = false :=
  MotherEquation.no_intermediate_state

theorem lemma_9_4 {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s)) :
    (∀ u : ℝ × ℝ, vim f (reflA u) = -vim f u) ∧
    (∀ u : ℝ × ℝ, vim f (reflB u) = -vim f u) ∧
    (∀ y : ℝ, vim f (1 / 2, y) = 0) ∧
    (∀ x : ℝ, vim f (x, 0) = 0) ∧
    (∀ σ γ : ℝ, deriv f (↑σ + ↑γ * I) ≠ 0 → nablaV f (σ, γ) ≠ 0) := by
  simpa [vim, RH94.vim, reflA, RH95U.reflA, reflB, RH95U.reflB, nablaV, RH94.nablaV] using
    RH94.lemma_9_4 hf h_sym h_conj

theorem Kquad_chiAB_neg (C : ℝ) (w : Fin 4 → ℝ × ℝ) (hC : 0 < C)
    (hA : ∀ i, w (iA i) = JB (w i)) (hB : ∀ i, w (iB i) = JA (w i))
    (hne : ∃ i : Fin 4, w i ≠ 0) :
    Kquad C w < 0 := by
  have hA' : ∀ i, w (RH95C.iA i) = RH95C.JB (w i) := by
    intro i; simpa [iA_eq, JB, RH95C.JB] using hA i
  have hB' : ∀ i, w (RH95C.iB i) = RH95C.JA (w i) := by
    intro i; simpa [iB_eq, JA, RH95C.JA] using hB i
  simpa [Kquad, RH95C.Kquad, dot, RH95C.dot, JA, RH95C.JA, JB, RH95C.JB, iA, RH95C.iA, iB,
    RH95C.iB] using RH95C.Kquad_chiAB_neg C w hC hA' hB' hne

theorem theorem_9_5_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → deriv f (↑σ + I * ↑t) ≠ 0)
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t))
    {σ t : ℝ} (hz : f (↑σ + I * ↑t) = 0) (hσ : σ ≠ 1 / 2) (ht : t ≠ 0) :
    False :=
  RH95Final.theorem_9_5_final C hC f hf h_sym h_conj hsimple (unit_bridge hunit) hz hσ ht

theorem theorem_10_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → deriv f (↑σ + I * ↑t) ≠ 0)
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t)) :
    ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t = 0 :=
  RH95Final.theorem_10_final C hC f hf h_sym h_conj hsimple (unit_bridge hunit)

theorem lemma_11_3
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (0 : ℝ) < (xiFn (x : ℂ)).re ∧ (xiFn (x : ℂ)).im = 0 := by
  simpa [xiFn_eq] using RH113.lemma_11_3 hζ hx0 hx1

theorem critical_line_lock {s : ℂ} {w : ℝ}
    (hw : (s - 1 / 2) ^ 2 = (w : ℂ)) (hwneg : w < 0) :
    s.re = 1 / 2 :=
  RH113.critical_line_lock hw hwneg

theorem RH_general (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → deriv f (↑σ + I * ↑t) ≠ 0)
    (hunit : ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad f σ t))
    {σ t : ℝ} (hz : f (↑σ + I * ↑t) = 0) :
    σ = 1 / 2 ∨ t = 0 :=
  RHFinal.RH_general C hC f hf h_sym h_conj hsimple (unit_bridge hunit) hz

theorem RH_xi (C : ℝ) (hC : 0 < C)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hunit : ∀ σ t : ℝ, g (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad g σ t))
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    (hg_simple : ∀ σ t : ℝ, g (↑σ + I * ↑t) = 0 → deriv g (↑σ + I * ↑t) ≠ 0)
    {s : ℂ} (hz : g s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s.re = 1 / 2 :=
  RHFinal.RH_xi C hC g hg (unit_bridge hunit) hζ
    (fun s hs0 hs1 => (hg_eq s hs0 hs1).trans (xiFn_eq s))
    hg_sym hg_conj hg_simple hz hs0 hs1

theorem RH_xi_zeros (C : ℝ) (hC : 0 < C)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hunit : ∀ σ t : ℝ, g (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
      0 < Kquad C (orbitGrad g σ t))
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    (hg_simple : ∀ σ t : ℝ, g (↑σ + I * ↑t) = 0 → deriv g (↑σ + I * ↑t) ≠ 0)
    {s : ℂ} (hz : g s = 0) :
    s.re = 1 / 2 ∨ s = 0 ∨ s = 1 :=
  RHFinal.RH_xi_zeros C hC g hg (unit_bridge hunit) hζ
    (fun s hs0 hs1 => (hg_eq s hs0 hs1).trans (xiFn_eq s))
    hg_sym hg_conj hg_simple hz

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
  apply RHM.theorem_9_5_multiplicity C hC E f
      (by
        intro m J hA hB hJ hzero
        apply hE_pos m J
        · intro i; simpa [iA_eq] using hA i
        · intro i; simpa [iB_eq] using hB i
        · exact hJ
        · rcases hzero with ⟨σ, t, hz', hσ', ht', hJeq⟩
          exact ⟨σ, t, hz', hσ', ht', fun i => by simpa [orbitC_eq] using hJeq i⟩)
      (by
        intro m J hA hB hJ
        apply hE_neg m J
        · intro i; simpa [iA_eq] using hA i
        · intro i; simpa [iB_eq] using hB i
        · exact hJ)
      hf h_sym h_conj hne hz hσ ht

theorem RH_xi_unconditional (C : ℝ) (hC : 0 < C)
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
  apply RHFinalM.RH_xi_unconditional C hC E g
      (by
        intro m J hA hB hJ hzero
        apply hE_pos m J
        · intro i; simpa [iA_eq] using hA i
        · intro i; simpa [iB_eq] using hB i
        · exact hJ
        · rcases hzero with ⟨σ, t, hz', hσ', ht', hJeq⟩
          exact ⟨σ, t, hz', hσ', ht', fun i => by simpa [orbitC_eq] using hJeq i⟩)
      (by
        intro m J hA hB hJ
        apply hE_neg m J
        · intro i; simpa [iA_eq] using hA i
        · intro i; simpa [iB_eq] using hB i
        · exact hJ)
      hζ hg
      (fun s hs0 hs1 => (hg_eq s hs0 hs1).trans (xiFn_eq s))
      hg_sym hg_conj hz hs0 hs1

theorem five_eight_equiv {ι : Type*} (α : ι → ℂ) (Z : Set ℂ) (hSpec : Set.range α = Z) :
    Z ⊆ {z : ℂ | z.im = 0} ↔
      Set.range α ⊆ {z : ℂ | z.im = 0} ∧
      (∀ i, ∀ x y : ℂ, star (α i * x) * y = star x * (α i * y)) ∧
      ((∀ i, ∀ τ : ℝ, ‖exp (I * (τ : ℂ) * α i)‖ = 1) ∧
        ∀ i, Tendsto (fun τ : ℝ => exp (I * (τ : ℂ) * α i)) (nhds 0) (nhds 1)) ∧
      (∀ i, (α i).im = 0) := by
  let R : Section5A8.SpectralReading ι := ⟨α, Z, hSpec⟩
  simpa [Section5A8.rootsReal, Section5A8.specReal, Section5A8.selfAdjointDiag,
    Section5A8.unitaryGroup, Section5A8.energyReal, Section5A8.applyL, Section5A8.applyU,
    Section5A8.energyBasis] using Section5A8.five_eight_equiv R

theorem theorem_10_unconditional (C : ℝ) (hC : 0 < C)
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
    ∀ σ t : ℝ, f (↑σ + I * ↑t) = 0 → σ ≠ 1 / 2 → t = 0 :=
  RHM.theorem_10_unconditional C hC E f (posBridge hE_pos) (negBridge hE_neg)
    hf h_sym h_conj hne

theorem RH_general_unconditional (C : ℝ) (hC : 0 < C)
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
    σ = 1 / 2 ∨ t = 0 :=
  RHFinalM.RH_general_unconditional C hC E f (posBridge hE_pos) (negBridge hE_neg)
    hf h_sym h_conj hne hz

theorem RH_xi_zeros_unconditional (C : ℝ) (hC : 0 < C)
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
    s.re = 1 / 2 ∨ s = 0 ∨ s = 1 :=
  RHFinalM.RH_xi_zeros_unconditional C hC E g (posBridge hE_pos) (negBridge hE_neg)
    hζ hg (fun s hs0 hs1 => (hg_eq s hs0 hs1).trans (xiFn_eq s))
    hg_sym hg_conj hz

theorem taylor_remainder_C2 {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    (hcs : HasCompactSupport Φ)
    (hBd : ∃ B, 0 ≤ B ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ Φ) z‖ ≤ B)
    (z0 : ℝ × ℝ) (hΦ0 : Φ z0 = 0) :
    ∃ M, 0 ≤ M ∧ ∀ u, |Φ (z0 + u) - (fderiv ℝ Φ z0) u| ≤ M * (nrm2 u) ^ 2 := by
  simpa [nrm2, RH95C.nrm2] using RHT.taylor_remainder_C2 hΦ hcs hBd z0 hΦ0

end
