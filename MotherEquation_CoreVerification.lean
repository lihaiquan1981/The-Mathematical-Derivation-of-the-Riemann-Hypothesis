module

/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

@[expose] public section

namespace MotherEquation

theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.lt_trichotomy a 0 with hlt | heq | hgt
  · have hp : 0 < (-a) := by grind
    have h2 : 0 < (-a) * (-a) := Int.mul_pos hp hp
    grind
  · grind
  · have h2 : 0 < a * a := Int.mul_pos hgt hgt
    grind

theorem int_sq_pos (a : Int) (h : a ≠ 0) : 0 < a * a := by
  rcases Int.lt_trichotomy a 0 with hlt | heq | hgt
  · have hp : 0 < (-a) := by grind
    have h2 : 0 < (-a) * (-a) := Int.mul_pos hp hp
    grind
  · grind
  · exact Int.mul_pos hgt hgt

namespace V4

abbrev G := Bool × Bool

def mul (x y : G) : G := (x.1 != y.1, x.2 != y.2)
def one : G := (false, false)
def A : G := (true, false)
def B : G := (false, true)
def AB : G := (true, true)

theorem mul_assoc : ∀ x y z : G, mul (mul x y) z = mul x (mul y z) :=
  fun ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ => by
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem mul_comm : ∀ x y : G, mul x y = mul y x :=
  fun ⟨a, b⟩ ⟨c, d⟩ => by cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem one_mul : ∀ x : G, mul one x = x :=
  fun ⟨a, b⟩ => by cases a <;> cases b <;> decide

theorem mul_one : ∀ x : G, mul x one = x :=
  fun ⟨a, b⟩ => by cases a <;> cases b <;> decide

theorem mul_self_invol : ∀ x : G, mul x x = one :=
  fun ⟨a, b⟩ => by cases a <;> cases b <;> decide

theorem A_mul_B : mul A B = AB := by decide
theorem A_invol : mul A A = one := by decide
theorem B_invol : mul B B = one := by decide
theorem AB_invol : mul AB AB = one := by decide

def chi0 (_ : G) : Int := 1
def chiA (x : G) : Int := if x.1 then -1 else 1
def chiB (x : G) : Int := if x.2 then -1 else 1
def chiAB (x : G) : Int := chiA x * chiB x

theorem chiAB_table :
    chiAB one = 1 ∧ chiAB A = -1 ∧ chiAB B = -1 ∧ chiAB AB = 1 :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem chiAB_is_hom : ∀ x y : G, chiAB (mul x y) = chiAB x * chiAB y :=
  fun ⟨a, b⟩ ⟨c, d⟩ => by cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem ortho_AB_A :
    chiAB one * chiA one + chiAB A * chiA A + chiAB B * chiA B + chiAB AB * chiA AB = 0 := by
  decide

theorem ortho_AB_B :
    chiAB one * chiB one + chiAB A * chiB A + chiAB B * chiB B + chiAB AB * chiB AB = 0 := by
  decide

theorem ortho_AB_0 :
    chiAB one * chi0 one + chiAB A * chi0 A + chiAB B * chi0 B + chiAB AB * chi0 AB = 0 := by
  decide

theorem ortho_AB_self :
    chiAB one ^ 2 + chiAB A ^ 2 + chiAB B ^ 2 + chiAB AB ^ 2 = 4 := by
  decide

def actA (p : G) : G := (!p.1, p.2)
def actB (p : G) : G := (p.1, !p.2)
def actAB (p : G) : G := actA (actB p)

theorem orbit_generic_distinct :
    ∀ p : G, p ≠ actA p ∧ p ≠ actB p ∧ actA p ≠ actB p ∧
      p ≠ actAB p ∧ actA p ≠ actAB p ∧ actB p ≠ actAB p :=
  fun ⟨a, b⟩ => by cases a <;> cases b <;> decide

theorem orbit_collapsed_pair : ∀ d : Bool, d ≠ !d := by
  intro d; cases d <;> decide

theorem orbit_stabilizer_certificate :
    4 * 1 = 4 ∧ 2 * 2 = 4 ∧ 1 * 4 = 4 := ⟨rfl, rfl, rfl⟩

end V4

abbrev V4v := Int × Int × Int × Int

def smul4 (s : Int) (v : V4v) : V4v := (s * v.1, s * v.2.1, s * v.2.2.1, s * v.2.2.2)
def vadd4 (u v : V4v) : V4v := (u.1 + v.1, u.2.1 + v.2.1, u.2.2.1 + v.2.2.1, u.2.2.2 + v.2.2.2)
def dot4 (u v : V4v) : Int := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2.1 * v.2.2.1 + u.2.2.2 * v.2.2.2

def v0 : V4v := (1, 1, 1, 1)
def vA : V4v := (1, -1, 1, -1)
def vB : V4v := (1, 1, -1, -1)
def vAB : V4v := (1, -1, -1, 1)

def gK (C : Int) (v : V4v) : V4v :=
  (C * (v.2.1 + v.2.2.1), C * (v.1 + v.2.2.2), C * (v.1 + v.2.2.2), C * (v.2.1 + v.2.2.1))

def rK (C ε : Int) (v : V4v) : V4v := vadd4 (gK C v) (smul4 (2 * ε) v)

theorem gK_eig_chi0 (C : Int) : gK C v0 = smul4 (2 * C) v0 := by
  simp [gK, v0, smul4]; grind

theorem gK_eig_chiA (C : Int) : gK C vA = smul4 0 vA := by
  simp [gK, vA, smul4]

theorem gK_eig_chiB (C : Int) : gK C vB = smul4 0 vB := by
  simp [gK, vB, smul4]

theorem gK_eig_chiAB (C : Int) : gK C vAB = smul4 (-2 * C) vAB := by
  simp [gK, vAB, smul4]; grind

theorem rK_eig_chiAB (C ε : Int) : rK C ε vAB = smul4 (-2 * C + 2 * ε) vAB := by
  simp [rK, gK, vAB, smul4, vadd4]; grind

theorem rK_eig_chi0 (C ε : Int) : rK C ε v0 = smul4 (2 * C + 2 * ε) v0 := by
  simp [rK, gK, v0, smul4, vadd4]; grind

theorem rK_eig_chiA (C ε : Int) : rK C ε vA = smul4 (2 * ε) vA := by
  simp [rK, gK, vA, smul4, vadd4]

theorem rK_eig_chiB (C ε : Int) : rK C ε vB = smul4 (2 * ε) vB := by
  simp [rK, gK, vB, smul4, vadd4]

theorem spectrum_complete (v : V4v) :
    let s0 := v.1 + v.2.1 + v.2.2.1 + v.2.2.2
    let sA := v.1 - v.2.1 + v.2.2.1 - v.2.2.2
    let sB := v.1 + v.2.1 - v.2.2.1 - v.2.2.2
    let sAB := v.1 - v.2.1 - v.2.2.1 + v.2.2.2
    smul4 4 v = vadd4 (vadd4 (smul4 s0 v0) (smul4 sA vA))
                      (vadd4 (smul4 sB vB) (smul4 sAB vAB)) := by
  simp [smul4, vadd4, v0, vA, vB, vAB]; grind

theorem energy_expansion (C ε : Int) (v : V4v) :
    let s0 := v.1 + v.2.1 + v.2.2.1 + v.2.2.2
    let sA := v.1 - v.2.1 + v.2.2.1 - v.2.2.2
    let sB := v.1 + v.2.1 - v.2.2.1 - v.2.2.2
    let sAB := v.1 - v.2.1 - v.2.2.1 + v.2.2.2
    4 * dot4 v (rK C ε v)
      = (2 * C + 2 * ε) * (s0 * s0) + 2 * ε * (sA * sA + sB * sB)
        + (-2 * C + 2 * ε) * (sAB * sAB) := by
  simp [dot4, rK, gK, smul4, vadd4]; grind

theorem unitarity_sign (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    -2 * C + 2 * ε < 0 ∧ 2 * C + 2 * ε > 0 ∧ 2 * ε > 0 := by
  grind

theorem chiAB_pure_energy_negative (C ε s : Int) (hC : C > ε) (_hε : ε > 0) (hs : s ≠ 0) :
    dot4 (smul4 s vAB) (rK C ε (smul4 s vAB)) < 0 := by
  have h1 : 0 < s * s := int_sq_pos s hs
  have h2 : -2 * C + 2 * ε < 0 := by grind
  have h3 : 0 < 2 * C - 2 * ε := by grind
  have h4 : 0 < (s * s) * (2 * C - 2 * ε) := Int.mul_pos h1 h3
  have hid : dot4 (smul4 s vAB) (rK C ε (smul4 s vAB))
      = 4 * (s * s) * (-2 * C + 2 * ε) := by
    simp [dot4, rK, gK, smul4, vadd4, vAB]; grind
  rw [hid]
  grind

abbrev V2 := Int × Int

def smul2 (s : Int) (u : V2) : V2 := (s * u.1, s * u.2)

def gC (C : Int) (u : V2) : V2 := (C * (u.1 + u.2), C * (u.1 + u.2))
def rC (C ε : Int) (u : V2) : V2 := ((gC C u).1 + 2 * ε * u.1, (gC C u).2 + 2 * ε * u.2)

def w1 : V2 := (1, 1)
def w2 : V2 := (1, -1)

theorem collapse_eig_sym (C ε : Int) : rC C ε w1 = smul2 (2 * C + 2 * ε) w1 := by
  simp [rC, gC, smul2, w1]; grind

theorem collapse_eig_asym (C ε : Int) : rC C ε w2 = smul2 (2 * ε) w2 := by
  simp [rC, gC, smul2, w2]

theorem collapse_stable (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    2 * C + 2 * ε > 0 ∧ 2 * ε > 0 := by grind

abbrev V8 := Int × Int × Int × Int × Int × Int × Int × Int

def W8 (a b : Int) : V8 := (a, b, a, -b, -a, b, -a, -b)

def g8 (C : Int) (w : V8) : V8 :=
  match w with
  | (x1, y1, x2, y2, x3, y3, x4, y4) =>
    (C * (-x2 + x3), C * (y2 - y3),
     C * (-x1 + x4), C * (y1 - y4),
     C * (-x4 + x1), C * (y4 - y1),
     C * (-x3 + x2), C * (y3 - y2))

def smul8 (s : Int) (w : V8) : V8 :=
  match w with
  | (x1, y1, x2, y2, x3, y3, x4, y4) =>
    (s * x1, s * y1, s * x2, s * y2, s * x3, s * y3, s * x4, s * y4)

def vadd8 (u v : V8) : V8 :=
  match u, v with
  | (x1, y1, x2, y2, x3, y3, x4, y4), (x1', y1', x2', y2', x3', y3', x4', y4') =>
    (x1 + x1', y1 + y1', x2 + x2', y2 + y2', x3 + x3', y3 + y3', x4 + x4', y4 + y4')

def r8 (C ε : Int) (w : V8) : V8 := vadd8 (g8 C w) (smul8 (2 * ε) w)

def dot8 (u v : V8) : Int :=
  match u, v with
  | (x1, y1, x2, y2, x3, y3, x4, y4), (x1', y1', x2', y2', x3', y3', x4', y4') =>
    x1 * x1' + y1 * y1' + x2 * x2' + y2 * y2' + x3 * x3' + y3 * y3' + x4 * x4' + y4 * y4'

theorem jet_eigenvalue (C ε a b : Int) :
    r8 C ε (W8 a b) = smul8 (-2 * C + 2 * ε) (W8 a b) := by
  simp [r8, g8, W8, smul8, vadd8]; grind

theorem jet_energy (C ε a b : Int) :
    dot8 (W8 a b) (r8 C ε (W8 a b)) = 4 * (a * a + b * b) * (-2 * C + 2 * ε) := by
  simp [dot8, r8, g8, W8, smul8, vadd8]; grind

theorem jet_negative (C ε a b : Int) (hC : C > ε) (_hε : ε > 0)
    (hne : a ≠ 0 ∨ b ≠ 0) :
    dot8 (W8 a b) (r8 C ε (W8 a b)) < 0 := by
  have ha2 : 0 ≤ a * a := int_sq_nonneg a
  have hb2 : 0 ≤ b * b := int_sq_nonneg b
  have hpos : 0 < a * a + b * b := by
    rcases hne with ha | hb
    · have := int_sq_pos a ha; grind
    · have := int_sq_pos b hb; grind
  have h4 : 0 < 4 * (a * a + b * b) := by grind
  have h5 : 0 < 2 * C - 2 * ε := by grind
  have h6 : 0 < 4 * (a * a + b * b) * (2 * C - 2 * ε) := Int.mul_pos h4 h5
  rw [jet_energy]
  grind

def minEig (collapsed : Bool) (C ε : Int) : Int :=
  if collapsed then 2 * ε else -2 * C + 2 * ε

theorem phase_cliff (C ε : Int) (hC : C > ε) (hε : ε > 0) :
    minEig false C ε < 0 ∧ minEig true C ε > 0 ∧
    minEig true C ε - minEig false C ε = 2 * C := by
  simp [minEig]; grind

theorem no_intermediate_state : ∀ b : Bool, b = true ∨ b = false := by
  intro b; cases b <;> simp

theorem mother_equation_core_certificate (C ε : Int) (hC : C > ε) (hε : ε > 0) :

    (-2 * C + 2 * ε < 0)

    ∧ (2 * C + 2 * ε > 0 ∧ 2 * ε > 0)

    ∧ (2 * C > 0) := by
  grind

end MotherEquation

#print axioms MotherEquation.gK_eig_chiAB
#print axioms MotherEquation.spectrum_complete
#print axioms MotherEquation.energy_expansion
#print axioms MotherEquation.chiAB_pure_energy_negative
#print axioms MotherEquation.collapse_eig_sym
#print axioms MotherEquation.jet_eigenvalue
#print axioms MotherEquation.jet_energy
#print axioms MotherEquation.jet_negative
#print axioms MotherEquation.phase_cliff
#print axioms MotherEquation.mother_equation_core_certificate
#print axioms MotherEquation.V4.chiAB_is_hom
#print axioms MotherEquation.V4.orbit_generic_distinct

end
