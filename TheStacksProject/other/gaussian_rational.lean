import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image
import Mathlib.Tactic.Ring
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties

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

namespace AlgebraicGeometry

def ℚ_i : Scheme :=  Spec (CommRingCat.of GaussianRational)

instance : Nontrivial GaussianRational where
  exists_pair_ne := by
    use 0, 1
    simp [Rational]

instance : IsIntegral ℚ_i where
  nonempty := by
    let ⟨g, h⟩ := Ideal.exists_maximal GaussianRational
    exact ⟨g, h.isPrime⟩
  component_integral := by
    intro U
    intro hu
    let r := ↑Γ(ℚ_i, U)
    have : IsLeftCancelMulZero r := ⟨by
      rintro a b c h eq
      unfold_let r at a b c
      unfold Scheme.toLocallyRingedSpace at a b c
      unfold ℚ_i at a b c
      unfold Spec at a b c
      dsimp at a b c
      unfold Spec.structureSheaf at a b c
      unfold structurePresheafInCommRing  at a b c
      unfold structureSheafInType at a b c
      unfold TopCat.subsheafToTypes StructureSheaf.isLocallyFraction at a b c
      dsimp at a b c
      unfold StructureSheaf.isFractionPrelocal at a b c
      unfold Ne at h
      rw [Subtype.ext_iff] at h
      rw [Subtype.ext_iff] at eq
      unfold HMul.hMul at eq
      unfold instHMul at eq
      rw [← Subtype.ext_iff] at eq
      simp at eq
      let getType := fun {T: Type}(_ : T) => T
      let getMul := fun {T: Type} [m: Mul T] (_ : T) => m
      sorry
      ⟩
    sorry

end AlgebraicGeometry


--{x : ℂ //  Rational x.im ∧ Rational x.re}
