import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Push

class PlaneGeometry where
  Point : Type
  Line : Type
  -- Incidence relation (when a point lies on a line)
  incident : Point → Line → Prop

def isIncident {P : PlaneGeometry} (p : P.Point) (l : P.Line) : Prop :=
  P.incident p l

infix:50 " ∈ " => isIncident

open PlaneGeometry

-- Axioms of Incidence
class IncidencePlaneGeometry extends PlaneGeometry where
  -- Axiom I₁: Every line has at least one point on it and at least one point not on it
  axiom_I₁ : ∀ l : Line, 
    (∃ p : Point, p ∈ l) ∧ 
    (∃ p : Point, ¬(p ∈ l))
  
  -- Axiom I₂: For any two distinct points, there exists a unique line containing them
  axiom_I₂ : ∀ (p q : Point), p ≠ q → 
    ∃! l : Line, p ∈ l ∧ q ∈ l

def intersect {P : PlaneGeometry} (l m : Line) : Prop :=
  ∃ p : Point, p ∈ l ∧ p ∈ m

-- Proposition 1.1: Two distinct lines either don't intersect or intersect at exactly one point
theorem prop_1_1 {P : IncidencePlaneGeometry}
    (l m : P.Line) (h : l ≠ m) : 
    (¬intersect l m) ∨ (∃! p : P.Point, p ∈ l ∧ p ∈ m) := by
    by_cases h_int : intersect l m
    case neg =>
        left
        exact h_int
    case pos =>
        right
        obtain ⟨p, h_int_p⟩ := h_int
        apply ExistsUnique.intro p
        exact h_int_p
        intro q h_int_q
        apply Classical.byContradiction
        intro h_contra
        push_neg at h_contra
        obtain ⟨u, h_l_exists, h_l_unique⟩ := P.axiom_I₂ p q (Ne.symm h_contra)
        have h_l_eq_u := h_l_unique l ⟨h_int_p.1, h_int_q.1⟩
        have h_m_eq_u := h_l_unique m ⟨h_int_p.2, h_int_q.2⟩
        have h_eq : l = m := by rw [h_l_eq_u, h_m_eq_u]
        contradiction

class OrderedPlaneGeometry extends PlaneGeometry where
  -- Betweenness relation: between a b c means "b is between a and c"
  between : Point → Point → Point → Prop

-- Shorthand notation for betweenness
def isBetween {P : OrderedPlaneGeometry} (a b c : P.Point) : Prop :=
  P.between a b c


class OrderAxioms (P : OrderedPlaneGeometry) where
  -- Axiom II₁: Given three distinct points on a line, exactly one is between the other two
  axiom_II₁ : ∀ (a b c : P.Point) (l : P.Line), 
    a ≠ b ∧ b ≠ c ∧ a ≠ c → 
    a ∈ l ∧ b ∈ l ∧ c ∈ l → 
    (isBetween a b c ∧ ¬isBetween b a c ∧ ¬isBetween a c b) ∨
    (isBetween a c b ∧ ¬isBetween c a b ∧ ¬isBetween a b c) ∨
    (isBetween b a c ∧ ¬isBetween a b c ∧ ¬isBetween b c a)

