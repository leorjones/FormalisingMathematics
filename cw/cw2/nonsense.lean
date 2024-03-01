import Mathlib.Tactic
variable (X : Type)(x : X)
variable (G H : Type)[Group G][MulAction G X]
variable (H : Subgroup G)
variable {a b g : G}

def orbit (x : X) : Set X := { b | ∃ g : G, g • x = b }

def stabilizer (x : X) : Set G := { g | g • x = x }

def orbit_size (x : X) : ℕ := Fintype.card (orbit x)

yoo
