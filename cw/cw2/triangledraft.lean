import Mathlib.Tactic

variable (n : ℕ)

def n_set : Set ℕ := Finset.range n

variable (a1 a2 a3 b1 b2 b3 c1 : n_set n)

def n7 := n_set (n) × n_set (n) × n_set (n) × n_set (n) ×  n_set (n) × n_set (n) × n_set (n)

def example_element : n7 n := (a1, a2, a3, b1, b2, b3, c1)

inductive D₃
| e : D₃     -- Identity
| r₀ : D₃    -- Rotation by 120 degrees clockwise
| r₁  : D₃   -- Rotation by 240 degrees clockwise
| s₀  : D₃   -- Reflect about line through top vertex
| s₁  : D₃   -- Reflect about line through left vertex
| s₂  : D₃   -- Reflect about line through right vertex

def rotation_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a3, a1, b2, b3, b1, c1)

def reflection_0_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a1, a3, a2, b3, b2, b1, c1)

def reflection_1_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a3, a2, a1, b2, b1, b3, c1)

def reflection_2_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a1, a3, b1, b3, b2, c1)

def myaction2: D₃ → (n7 n → n7 n)
| D₃.e => id
| D₃.r₀ => rotation_funct n
| D₃.r₁ => (rotation_funct n) ∘ (rotation_funct n)
| D₃.s₀ => reflection_0_funct n
| D₃.s₁ => reflection_1_funct n
| D₃.s₂ => reflection_2_funct n

def myaction3: DihedralGroup 3 → (n7 n → n7 n)
| D₃.e => id
| D₃.r₀ => rotation_funct n
| D₃.r₁ => (rotation_funct n) ∘ (rotation_funct n)
| D₃.s₀ => reflection_0_funct n
| D₃.s₁ => reflection_1_funct n
| D₃.s₂ => reflection_2_funct n

instance : mul_action D₃ n7 :=
