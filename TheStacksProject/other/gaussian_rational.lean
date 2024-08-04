import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image
import Mathlib.Tactic.Ring

def Rational (x: ℝ) := ¬ Irrational x

theorem RationalMulClosed {x y: ℝ} : Rational x → Rational y → Rational (x * y) := by
  simp [Rational, Irrational]
  intro a
  intro b
  intro c
  intro d
  use a * c
  simp [Rat.cast_mul, b, d]

theorem RationalAddClosed {x y: ℝ} : Rational x → Rational y → Rational (x + y) := by
  simp [Rational, Irrational]
  intro a
  intro b
  intro c
  intro d
  use a + c
  simp [Rat.cast_add, b, d]

theorem RationalSubClosed {x y: ℝ} : Rational x → Rational y → Rational (x - y) := by
  simp [Rational, Irrational]
  intro a
  intro b
  intro c
  intro d
  use a - c
  simp [Rat.cast_add, b, d]

theorem RationalNegClosed {x: ℝ} : Rational x  → Rational (-x) := by
  simp [Rational, Irrational]
  intro a
  intro b
  use -a
  simp [Rat.cast_neg, b]

example : 1 ∈ {x : ℝ | Rational x} := by
  simp [Rational]

def GaussianRational : Subring ℂ :=
{
  carrier := {x : ℂ | Rational x.im ∧ Rational x.re}
  one_mem' := by simp [Rational],
  mul_mem' := by
    intro a
    intro b
    intro c
    intro d
    simp [] at c
    simp [] at d
    simp []
    have i := RationalAddClosed (RationalMulClosed c.right d.left) (RationalMulClosed c.left d.right)
    have j := RationalSubClosed (RationalMulClosed c.right d.right) (RationalMulClosed c.left d.left)
    exact And.intro i j
  add_mem' := by
    intro a
    intro b
    intro c
    intro d
    simp [] at c
    simp [] at d
    simp []
    have i := RationalAddClosed c.right d.right
    have j := RationalAddClosed c.left d.left
    exact And.intro j i
  zero_mem' := by simp [Rational],
  neg_mem' := by
    intro a
    intro b
    simp [] at b
    simp []
    have i := RationalNegClosed b.right
    have j := RationalNegClosed b.left
    exact And.intro j i
}

instance : CommRing GaussianRational := GaussianRational.toCommRing

--{x : ℂ //  Rational x.im ∧ Rational x.re}
