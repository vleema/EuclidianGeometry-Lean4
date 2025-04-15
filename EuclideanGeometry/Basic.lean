import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Push

namespace EuclidianGeometry

class Plane (α : Type) where
  Point : Type
  Line : Type

  -- Incidence relation (when a point lies on a line)
  incident : Point → Line → Prop

  -- Axiom I₁: Every line has at least one point on it and at least one point not on it
  axiom_I₁ : ∀ l : Line, 
    (∃ p : Point, incident p l) ∧ 
    (∃ p : Point, ¬(incident p l))
  
  -- Axiom I₂: For any two distinct points, there exists a unique line containing them
  axiom_I₂ : ∀ (p q : Point), p ≠ q → 
    ∃! l : Line, incident p l ∧ incident q l

open Plane

def isIncident {P : Plane α} (p : Point α) (l : Line α) : Prop :=
  incident p l

infix:50 " ∈ " => isIncident

def isNotIncident {P : Plane α} (p : Point α) (l : Line α) : Prop :=
  ¬(incident p l)

infix:50 " ∉ " => isIncident

def intersect {P : Plane α} (l m : Line α) : Prop :=
  ∃ p : Point α, p ∈ l ∧ p ∈ m

-- Proposition 1.1: Two distinct lines either don't intersect or intersect at exactly one point
theorem prop_1_1 {P : Plane α}
    (l m : Line α) (h : l ≠ m) : 
    (¬intersect l m) ∨ (∃! p : Point α, p ∈ l ∧ p ∈ m) := by
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

class OrderedPlane (α : Type) extends Plane α where
  -- Betweenness relation: between a b c means "b is between a and c"
  between : Point → Point → Point → Prop

-- Shorthand notation for betweenness
def isBetween {P : OrderedPlane α} (a b c : Point α) : Prop :=
  P.between a b c

structure SemiPlane (α : Type) (P : OrderedPlane α) where
  boundary        : Line α
  representative  : Point α 
  not_on_boundary : ¬(representative ∈ boundary)

-- Function to determine if a point is in a semi-plane
def inSemiPlane {α : Type} {P : OrderedPlane α} (p : Point α) (sp : SemiPlane α P) : Prop :=
  -- Either the point is the representative point
  p = sp.representative ∨
  -- Or the point and representative are on the same side of the boundary line
  -- This means that any line through p and the representative does not intersect the boundary
  (∀ l : Line α, p ∈ l → sp.representative ∈ l → ¬(intersect l sp.boundary)) ∨
  -- Or they're on a line that intersects the boundary at exactly one point,
  -- and the boundary point is between them (which means they're on the same side)
  (∃ l : Line α, p ∈ l ∧ sp.representative ∈ l ∧ 
    (∃! b : Point α, b ∈ l ∧ b ∈ sp.boundary ∧
      (isBetween p b sp.representative ∨ isBetween sp.representative b p)))

infix:50 " ∈ " => inSemiPlane

def notInSemiPlane {α : Type} {P : OrderedPlane α} (p : Point α) (sp : SemiPlane α P) : Prop := 
  ¬(inSemiPlane p sp)

infix:50 " ∉ " => notInSemiPlane

class OrderAxioms (P : OrderedPlane α) where
  -- Axiom II₁: Given three distinct points on a line, exactly one is between the other two
  axiom_II₁ : ∀ (a b c : Point α) (l : Line α), 
    a ≠ b ∧ b ≠ c ∧ a ≠ c → 
    a ∈ l ∧ b ∈ l ∧ c ∈ l → 
    (isBetween a b c ∧ ¬isBetween b a c ∧ ¬isBetween a c b) ∨
    (isBetween a c b ∧ ¬isBetween c a b ∧ ¬isBetween a b c) ∨
    (isBetween b a c ∧ ¬isBetween a b c ∧ ¬isBetween b c a)

  -- Axiom II₂ : Given two distinct points, exists a least one point in between them
  axiom_II₂ : ∀ (a b : Point α), a ≠ b → ∃ (c : Point α), isBetween a c b

  -- Axiom II₃ : A line determines exactly two distinct semi-planes
  axiom_II₃ : ∀ (l : Line α), ∃ (sp₁ sp₂ : SemiPlane α P), 
    (sp₁.boundary = l) ∧ (sp₂.boundary = l) ∧
    (∀ p : Point α, p ∉ l → (p ∈ sp₁ ↔ p ∉ sp₂))

def Segment (P : Plane α) := { pair : Point α × Point α // pair.1 ≠ pair.2 }

def mkSegment {P : Plane α} (a b : Point α) (h : a ≠ b) : Segment P :=
  ⟨(a, b), h⟩

def endpoints {P : Plane α} (s : Segment P) : Point α × Point α := s.val

structure Ray (P : OrderedPlane α) where
  origin    : Point α
  direction : Point α
  distinct  : origin ≠ direction

def pointOnRay {P : OrderedPlane α} (r : Ray P) (p : Point α) : Prop :=
  -- First condition: the point must be collinear with the ray's defining points
  (∃ l : Line α, r.origin ∈ l ∧ r.direction ∈ l ∧ p ∈ l) ∧
  -- Second condition: the point must be on the same side of the origin as the direction
  (p = r.origin ∨ 
   -- Either p is between origin and direction
   (isBetween r.origin p r.direction) ∨ 
   -- Or direction is between origin and p
   (isBetween r.origin r.direction p))

end EuclidianGeometry
