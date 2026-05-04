-- Author: Sudhir Murthy
-- Acknowledgements: I thank Eric Reck for his encouragement in this project. I would also like to thank John Mumma for his talk on Counting Arithmetic and his permission to attempt to formalize his theory in Lean4.
import Mathlib
--set_option trace.Meta.synthInstance true

namespace Counting_Arithmetic
universe u v

/-- The purpose of this definition is to construct functions in the usual constructive way in ZF. We will use this to extend the signature of the language by defined functions. Note Lean4's type theory freely uses choice so to be clear of the distinction, we introduce ``functionComprehension``. -/

noncomputable def functionComprehension {X:Type u} {Y:Type v} (φ : X → Y → Prop) (h : ∀ x : X, ∃! y : Y, φ x y) :
{f : X → Y // ∀ x : X, φ x (f x)} := by
  refine ⟨(fun x => Classical.choose ((h x).exists)), ?_⟩
  intro x
  exact Classical.choose_spec ((h x).exists)
/- We do not really use it yet, but maybe we will in the future so we keep it just in case.-/

/--A ``CountingArithmetic`` is a structure that axiomatizes the basic properties of counting arithmetic described by John Mumma. -/

class CountingArithmetic (I S : Type u)
    extends LinearOrder I, One I, Membership I S, Add S, Mul S where
  s    : I → I
  pr   : I → I → I
  isN    : I → Prop
  bar  : I → S
  C    : S → I

  I4 : ∀ i : I, i < s i
  I5 : ∀ i j : I, i < j → s i = j ∨ s i < j
  I6 : ∀ i j k p : I, i < j → pr i k < pr j p
  I7 : ∀ i j k : I, i < j → pr k i < pr k j
  I8 : ∀ i j : I, s (pr i j) = pr i (s j)
  I9 : isN 1 ∧ ∀ i : I, isN i → isN (s i)
  I10 : ∀ i j k : I, isN i → 1 ≤ i ∧ i < pr j k

  S1 : ∀ σ σ' : S, (∀ i : I, i ∈ σ ↔ i ∈ σ') → σ = σ'
  S2 : ∀ n : I, isN n → ∀ i : I, i ∈ bar n ↔ 1 ≤ i ∧ i ≤ n
  S3 : ∀ i j : I, bar (pr i j) = bar j
  S4 : ∀ σ σ' : S, ∀ i : I,
    i ∈ (σ + σ') ↔
      (∃ j : I, j ∈ σ ∧ i = pr 1 j) ∨
      (∃ j : I, j ∈ σ' ∧ i = pr (s 1) j)
  S5 : ∀ σ σ' : S, ∀ i : I,
    i ∈ (σ * σ') ↔
      ∃ j k : I, j ∈ σ ∧ k ∈ σ' ∧ i = pr j k
  S6 : ∀ φ : I → Prop, ∀ σ : S, { ρ : S // ∀ i : I, i ∈ ρ ↔ i ∈ σ ∧ φ i }

  C1 : ∀ σ : S, ∀ j : I, ∀ τ : S,
    (∀ i : I, i ∈ τ ↔ i ∈ σ ∧ i ≤ j) →
    (j ∈ σ ∧ ∀ i : I, i ∈ σ → j ≤ i) →
    C τ = 1

  C2 : ∀ σ : S, ∀ j k : I, ∀ τ τ' : S,
  (∀ i : I, i ∈ τ ↔ i ∈ σ ∧ i ≤ j) →
  (∀ i : I, i ∈ τ' ↔ i ∈ σ ∧ i ≤ k) →
  (j ∈ σ ∧ k ∈ σ ∧ j < k ∧
    ∀ i : I, i ∈ σ → j < i → k ≤ i) →
  C τ' = s (C τ)

  C3 : ∀ δ σ σ' : S,
    ((∀ i : I, i ∈ δ → i ∈ σ * σ') ∧
    (∀ i : I, i ∈ σ → ∃! j : I, j ∈ σ' ∧  pr i j ∈ δ) ∧
    (¬ ¬ ∃ i : I, i ∈ σ) ∧
    (C σ' < C σ)) →
    ∃ i j k : I, i ≠ j ∧ pr i k ∈ δ ∧ pr j k ∈ δ


variable {I S : Type u} [CountingArithmetic I S]
local notation "s" => CountingArithmetic.s (I := I) (S := S)
local notation "pr" => CountingArithmetic.pr (I := I) (S := S)
local notation "⟪" i ", " j "⟫" => pr i j
local notation "isN" => CountingArithmetic.isN (I := I) (S := S)
local notation "bar" => CountingArithmetic.bar (I := I) (S := S)
local notation "C" => CountingArithmetic.C (I := I) (S := S)
local notation "I4" => CountingArithmetic.I4 (I := I) (S := S)
local notation "I5" => CountingArithmetic.I5 (I := I) (S := S)
local notation "I6" => CountingArithmetic.I6 (I := I) (S := S)
local notation "I7" => CountingArithmetic.I7 (I := I) (S := S)
local notation "I8" => CountingArithmetic.I8 (I := I) (S := S)
local notation "I9" => CountingArithmetic.I9 (I := I) (S := S)
local notation "I10" => CountingArithmetic.I10 (I := I) (S := S)
local notation "S1" => CountingArithmetic.S1 (I := I) (S := S)
local notation "S2" => CountingArithmetic.S2 (I := I) (S := S)
local notation "S3" => CountingArithmetic.S3 (I := I) (S := S)
local notation "S4" => CountingArithmetic.S4 (I := I) (S := S)
local notation "S5" => CountingArithmetic.S5 (I := I) (S := S)
local notation "S6" => CountingArithmetic.S6 (I := I) (S := S)
local notation "C1" => CountingArithmetic.C1 (I := I) (S := S)
local notation "C2" => CountingArithmetic.C2 (I := I) (S := S)
local notation "C3" => CountingArithmetic.C3 (I := I) (S := S)


def InitialSegment (σ : S) (j : I) : S :=
  (S6 (fun i => i ≤ j) σ).1
lemma InitialSegment_spec (σ : S) (j : I) :
∀ i : I, i ∈ InitialSegment σ j ↔ i ∈ σ ∧ i ≤ j :=
  (S6 (fun i => i ≤ j) σ).2

def EmptyCollection :=
  (S6 (fun _ => False) (bar 1)).1
local notation "∅" => EmptyCollection (I := I) (S := S)
lemma EmptyCollection_spec : ∀ i : I, i ∉ ∅ := by
  intro i hi
  have h := (S6 (fun i => False) (bar 1)).2 i
  have h := h.mp hi
  exact h.2

def isSubset (σ σ' : S) : Prop :=
  ∀ i : I, i ∈ σ → i ∈ σ'
local infix:50 " ⊆₀ " => isSubset (I := I) (S := S)
def isFirst (j : I) (σ : S) : Prop :=
  j ∈ σ ∧ ∀ i : I, i ∈ σ → j ≤ i
def isNext (j k : I) (σ : S) : Prop :=
  j ∈ σ ∧ k ∈ σ ∧ j < k ∧ ∀ i : I, i ∈ σ → j < i → k ≤ i
def isNonEmpty (σ : S) : Prop :=
  ¬ ¬ ∃ i : I, i ∈ σ
def isInhabited (σ : S) : Prop :=
  ∃ i : I, i ∈ σ
def isFunc (δ σ σ' : S) : Prop :=
  (δ ⊆₀ σ * σ') ∧
  (∀ i : I, i ∈ σ → ∃! j : I, j ∈ σ' ∧  ⟪i, j⟫ ∈ δ)
def isInj (δ σ σ' : S) : Prop :=
  (δ ⊆₀ σ * σ') ∧
  (∀ i j k : I, i ∈ σ → j ∈ σ → k ∈ σ' →
    ⟪i, k⟫ ∈ δ → ⟪j, k⟫ ∈ δ → i = j)
def isSurj (δ σ σ' : S) : Prop :=
  (δ ⊆₀ σ * σ') ∧
  (∀ j : I, j ∈ σ' → ∃ i : I, i ∈ σ ∧ ⟪i, j⟫ ∈ δ)
def isBij (δ σ σ' : S) : Prop :=
  isFunc (I:=I) δ σ σ' ∧
  (∀ i j k : I, i ∈ σ → j ∈ σ → k ∈ σ' →
    ⟪i, k⟫ ∈ δ → ⟪j, k⟫ ∈ δ → i = j) ∧
  (∀ j : I, j ∈ σ' → ∃ i : I, i ∈ σ ∧ ⟪i, j⟫ ∈ δ)

lemma I1 : ∀ i : I, ¬ i < i := by
  intro i h
  exact (lt_self_iff_false i).mp  h

lemma I2 : ∀ i j k : I, i < j → j < k → i < k := by
  intro i j k
  exact (lt_trans)

lemma I3 : ∀ i j : I, i < j ∨  i = j ∨ j < i  := by
  intro i j
  exact (lt_trichotomy i j)

@[simp]
lemma I6' :
  ∀ i j k p : I, i < j → ⟪i, k⟫ < ⟪j, p⟫ := I6

@[simp]
lemma I7' :
  ∀ i j k : I, i < j → ⟪k, i⟫ < ⟪k, j⟫ :=  I7

@[simp]
lemma I8' :
  ∀ i j : I, s ⟪i, j⟫ = ⟪i, s j⟫ := I8

@[simp]
lemma I10':
  ∀ i j k : I, isN i → 1 ≤ i ∧ i < ⟪j, k⟫ := I10

@[simp]
lemma S3':
  ∀ i j : I, bar ⟪i, j⟫ = bar j := S3

@[simp]
lemma S4' :
  ∀ σ σ' : S, ∀ i : I,
    i ∈ (σ + σ') ↔
      (∃ j : I, j ∈ σ ∧ i = ⟪1, j⟫) ∨
      (∃ j : I, j ∈ σ' ∧ i = ⟪s 1, j⟫) := S4

@[simp]
lemma S5':
  (∀ σ σ' : S, ∀ i : I,
    i ∈ (σ * σ') ↔
    ∃ j k : I, j ∈ σ ∧ k ∈ σ' ∧ i = ⟪j, k⟫) :=  S5

lemma C1' : ∀ σ : S, ∀ j : I,
    (isFirst j σ) → C (InitialSegment σ j) = 1 := by
  intro σ j h
  apply C1 σ j (InitialSegment σ j)
  · intro i
    exact InitialSegment_spec σ j i
  · exact h

lemma C2' : ∀ σ : S, ∀ j k : I, isNext j k σ →
  C (InitialSegment σ k) = s (C (InitialSegment σ j)) := by
  intro σ j k h
  exact C2 σ j k
    (InitialSegment σ j)
    (InitialSegment σ k)
    (InitialSegment_spec σ j)
    (InitialSegment_spec σ k)
    h

lemma C3' : ∀ δ σ σ' : S,
    (isFunc (I:=I) δ σ σ' ∧ isNonEmpty (I:= I) σ ∧ C σ' < C σ) →
    ∃ i j k : I, i ≠ j ∧ ⟪i, k⟫ ∈ δ ∧ ⟪j, k⟫ ∈ δ := by
  intro δ σ σ' h
  exact C3 δ σ σ' ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

theorem pair_left_injective : ∀ i j k l : I, ⟪i, j⟫ = ⟪k, l⟫ → i = k := by
  intro i j k l h
  rcases I3 (S:=S) i k with hik | rfl | hki
  · exfalso
    have : ⟪i, j⟫ < ⟪k, l⟫ := I6 i k j l hik
    apply I1 (I:=I) (S:=S) ⟪i, j⟫
    · rw [← h] at this; exact this
  · rfl
  · exfalso
    have : ⟪k, l⟫ < ⟪i, j⟫ := I6 k i l j hki
    rw [← h] at this
    apply I1 (I:=I) (S:=S) ⟪i, j⟫
    exact this

theorem pair_right_injective : ∀ i j k l : I, ⟪i, j⟫ = ⟪k, l⟫ → j = l := by
  intro i j k l h
  have hik : i = k := pair_left_injective (I := I) (S := S) i j k l h
  subst hik
  rcases I3 (S := S) j l with hjl | rfl | hlj
  · exfalso
    have : ⟪i, j⟫ < ⟪i, l⟫ := I7 j l i hjl
    apply I1 (I := I) (S := S) ⟪i, j⟫
    rw [← h] at this
    exact this
  · rfl
  · exfalso
    have : ⟪i, l⟫ < ⟪i, j⟫ := I7 l j i hlj
    apply I1 (I := I) (S := S) ⟪i, j⟫
    rw [← h] at this
    exact this

def inverse_bij {δ σ σ' : S} (_ : isBij (I:=I) δ σ σ') : S := by
  refine (S6 (fun i => ∃ j k : I, i = ⟪j, k⟫ ∧ ⟪k, j⟫ ∈ δ) (σ' * σ)).1

theorem inverse_bij_spec {δ σ σ' : S} (h : isBij (I:=I) δ σ σ') :
  ∀ i : I, i ∈ inverse_bij h ↔ ∃ j k : I, i = ⟪j, k⟫ ∧ ⟪k, j⟫ ∈ δ := by
  intro i
  unfold inverse_bij
  let P : I → Prop :=
    fun i => ∃ j k : I, i = ⟪j, k⟫ ∧ ⟪k, j⟫ ∈ δ
  have hs6 := (S6 P (σ' * σ)).2 i
  constructor
  · intro hi
    exact (hs6.mp hi).2
  · intro hi
    rcases hi with ⟨j, k, hij, hkjδ⟩
    apply hs6.mpr
    constructor
    · have hδprod : ⟪k, j⟫ ∈ σ * σ' := h.1.1 ⟪k, j⟫ hkjδ
      rcases (S5 σ σ' ⟪k, j⟫).mp hδprod with ⟨a, b, ha, hb, hab⟩
      have hka : k = a :=
        pair_left_injective (I := I) (S := S) k j a b hab
      have hjb : j = b :=
        pair_right_injective (I := I) (S := S) k j a b hab
      have hk : k ∈ σ := by
        rw [hka]
        exact ha
      have hj : j ∈ σ' := by
        rw [hjb]
        exact hb
      exact (S5 σ' σ i).mpr ⟨j, k, hj, hk, hij⟩
    · exact ⟨j, k, hij, hkjδ⟩

theorem inverse_bij_isFunc (δ σ σ' : S) (h: isBij (I:=I) δ σ σ') :
  isFunc (I:=I) (inverse_bij h) σ' σ := by
  unfold isFunc
  constructor
  · intro i hi
    rcases (inverse_bij_spec (I := I) (S := S) h i).mp hi with
      ⟨j, k, hij, hkjδ⟩
    have hδprod : ⟪k, j⟫ ∈ σ * σ' := h.1.1 ⟪k, j⟫ hkjδ
    rcases (S5 σ σ' ⟪k, j⟫).mp hδprod with ⟨a, b, ha, hb, hab⟩
    have hka : k = a :=
      pair_left_injective (I := I) (S := S) k j a b hab
    have hjb : j = b :=
      pair_right_injective (I := I) (S := S) k j a b hab
    have hk : k ∈ σ := by
      rw [hka]
      exact ha
    have hj : j ∈ σ' := by
      rw [hjb]
      exact hb
    exact (S5 σ' σ i).mpr ⟨j, k, hj, hk, hij⟩
  · intro i hi
    rcases h.2.2 i hi with ⟨j, hjσ, hjiδ⟩
    refine ⟨j, ?_, ?_⟩
    · constructor
      · exact hjσ
      · exact (inverse_bij_spec (I := I) (S := S) h ⟪i, j⟫).mpr
          ⟨i, j, rfl, hjiδ⟩

    · intro y hy
      have hyσ : y ∈ σ := hy.1
      have hiyInv : ⟪i, y⟫ ∈ inverse_bij h := hy.2

      rcases (inverse_bij_spec (I := I) (S := S) h ⟪i, y⟫).mp hiyInv with
        ⟨a, b, hab, hbaδ⟩

      have hia : i = a :=
        pair_left_injective (I := I) (S := S) i y a b hab
      have hyb : y = b :=
        pair_right_injective (I := I) (S := S) i y a b hab

      have hyiδ : ⟪y, i⟫ ∈ δ := by
        rw [hyb, hia]
        exact hbaδ

      exact h.2.1 y j i hyσ hjσ hi hyiδ hjiδ

theorem order_independence_of_counts : ∀ δ σ σ' : S,
  isBij (I:=I) δ σ σ' → isNonEmpty (I:= I) σ →
  C σ = C σ' := by

  intro δ σ σ' h H

  have hFunc : isFunc (I := I) δ σ σ' := h.1
  have hInj :
      ∀ i j k : I, i ∈ σ → j ∈ σ → k ∈ σ' →
        ⟪i, k⟫ ∈ δ → ⟪j, k⟫ ∈ δ → i = j := h.2.1

  have hσ_of_memδ : ∀ x y : I, ⟪x, y⟫ ∈ δ → x ∈ σ := by
    intro x y hxy
    have hprod : ⟪x, y⟫ ∈ σ * σ' := hFunc.1 ⟪x, y⟫ hxy
    rcases (S5 σ σ' ⟪x, y⟫).mp hprod with ⟨a, b, ha, hb, hab⟩
    have hxa : x = a :=
      pair_left_injective (I := I) (S := S) x y a b hab
    rw [hxa]
    exact ha

  have hσ'_of_memδ : ∀ x y : I, ⟪x, y⟫ ∈ δ → y ∈ σ' := by
    intro x y hxy
    have hprod : ⟪x, y⟫ ∈ σ * σ' := hFunc.1 ⟪x, y⟫ hxy
    rcases (S5 σ σ' ⟪x, y⟫).mp hprod with ⟨a, b, ha, hb, hab⟩
    have hyb : y = b :=
      pair_right_injective (I := I) (S := S) x y a b hab
    rw [hyb]
    exact hb

  have H' : isNonEmpty (I:= I) σ' := by
    unfold isNonEmpty at H ⊢
    intro hf
    apply H
    rintro ⟨i, hi⟩
    have hiFunc := hFunc.2 i hi
    rcases hiFunc.exists with ⟨j, hjσ', _⟩
    exact hf ⟨j, hjσ'⟩

  have h_not_lt₁ : ¬ C σ' < C σ := by
    intro hlt
    rcases C3' (I := I) δ σ σ' ⟨hFunc, H, hlt⟩ with
      ⟨i, j, k, hij, hikδ, hjkδ⟩

    have hiσ : i ∈ σ := hσ_of_memδ i k hikδ
    have hjσ : j ∈ σ := hσ_of_memδ j k hjkδ
    have hkσ' : k ∈ σ' := hσ'_of_memδ i k hikδ

    have heq : i = j := hInj i j k hiσ hjσ hkσ' hikδ hjkδ
    exact hij heq

  have h_not_lt₂ : ¬ C σ < C σ' := by
    intro hlt

    have hInvFunc : isFunc (I := I) (inverse_bij h) σ' σ :=
      inverse_bij_isFunc δ σ σ' h

    rcases C3' (I := I) (inverse_bij h) σ' σ ⟨hInvFunc, H', hlt⟩ with
      ⟨i, j, k, hij, hikInv, hjkInv⟩

    rcases (inverse_bij_spec (I := I) (S := S) h ⟪i, k⟫).mp hikInv with
      ⟨a, b, hab, hbaδ⟩
    have hia : i = a :=
      pair_left_injective (I := I) (S := S) i k a b hab
    have hkb : k = b :=
      pair_right_injective (I := I) (S := S) i k a b hab

    have hkiδ : ⟪k, i⟫ ∈ δ := by
      rw [hkb, hia]
      exact hbaδ

    rcases (inverse_bij_spec (I := I) (S := S) h ⟪j, k⟫).mp hjkInv with
      ⟨a', b', hab', hb'a'δ⟩
    have hja' : j = a' :=
      pair_left_injective (I := I) (S := S) j k a' b' hab'
    have hkb' : k = b' :=
      pair_right_injective (I := I) (S := S) j k a' b' hab'

    have hkjδ : ⟪k, j⟫ ∈ δ := by
      rw [hkb', hja']
      exact hb'a'δ

    have hkσ : k ∈ σ := hσ_of_memδ k i hkiδ
    have hiσ' : i ∈ σ' := hσ'_of_memδ k i hkiδ
    have hjσ' : j ∈ σ' := hσ'_of_memδ k j hkjδ

    rcases hFunc.2 k hkσ with ⟨w, hw, huniq⟩

    have hiw : i = w := huniq i ⟨hiσ', hkiδ⟩
    have hjw : j = w := huniq j ⟨hjσ', hkjδ⟩

    exact hij (hiw.trans hjw.symm)

  exact le_antisymm
    (le_of_not_gt h_not_lt₁)
    (le_of_not_gt h_not_lt₂)

theorem s_injective : ∀i j:I, s i = s j → i = j := by
  intro i j h
  rcases I3 (S := S) i j with hlt | rfl | hgt
  · rcases I5 i j hlt with hlt' | hlt''
    · rw [h] at hlt'
      exfalso
      have := I4 j
      rw [hlt'] at this
      exact (lt_self_iff_false j).mp this
    · rw [h] at hlt''
      exfalso
      have := I4 j
      have : j < j := by exact I2 j (CountingArithmetic.s S j) j this hlt''
      exact (lt_self_iff_false j).mp this
  · rfl
  · rcases I5 j i hgt with hlt' | hlt''
    · rw [← h] at hlt'
      exfalso
      have := I4 i
      rw [hlt'] at this
      exact (lt_self_iff_false i).mp this
    · rw [← h] at hlt''
      exfalso
      have := I4 i
      have : i < i := by exact I2 i (CountingArithmetic.s S i) i this hlt''
      exact (lt_self_iff_false i).mp this

theorem bar_subset_bar_succ :
    ∀k:I, isN k → ∀x:I, x∈bar k → x∈bar (s k) := by
  intro k hk x hx
  have hsk : isN (s k) := I9.2 k hk
  have hx_bounds : 1 ≤ x ∧ x ≤ k := (S2 k hk x).mp hx
  apply (S2 (s k) hsk x).mpr
  constructor
  · exact hx_bounds.1
  · exact le_trans hx_bounds.2 (le_of_lt (I4 k))

theorem predecessor_in_bar :
 ∀k:I, isN k → ∀j:I, j ∈ bar k → j ≠ 1 →
 ∃!i:I, i ∈ bar k ∧ s i = j := by
    intro k hk j hj hjn1
    suffices exists_unique : (∃ i : I, i ∈ bar k ∧ s i = j) ∧
      (∀ i i' : I, i ∈ bar k → s i = j → i' ∈ bar k → s i' = j → i = i')
    · rcases exists_unique with ⟨⟨i, hi⟩, unq⟩
      use i; refine ⟨hi, ?_⟩
      intro y hy; specialize unq i y hi.1 hi.2 hy.1 hy.2;
      symm; exact unq
    constructor
    · let ρ:S := InitialSegment (bar (s k)) (s j)
      have ρ_spec : ∀ i : I, i ∈ ρ ↔ i ∈ bar (s k) ∧ i ≤ s j := InitialSegment_spec (bar (s k)) (s j)
      let ρ' : S := InitialSegment (bar (s k)) j
      have ρ'_spec : ∀ i : I, i ∈ ρ' ↔ i ∈ bar (s k) ∧ i ≤ j := InitialSegment_spec (bar (s k)) j
      let δ:S := (S6 (fun  q => (∃p:I, p∈ρ ∧ p<j ∧ q=⟪p,s p⟫) ∨ q=⟪j, 1⟫ ∨ q=⟪s j, j⟫) (ρ * ρ')).1
      have δ_spec : ∀ q : I, q ∈ δ ↔ q ∈ ρ * ρ' ∧ ((∃ p : I, p ∈ ρ ∧ p < j ∧ q = ⟪p, s p⟫) ∨ q = ⟪j, 1⟫ ∨ q = ⟪s j, j⟫) := by
        intro q
        exact (S6 (fun q => (∃ p : I, p ∈ ρ ∧ p < j ∧ q = ⟪p, s p⟫) ∨ q = ⟪j, 1⟫ ∨ q = ⟪s j, j⟫) (ρ * ρ')).2 q
      have δ_isFunc : isFunc (I := I) δ ρ ρ' := by
        constructor
        · intro q hq
          specialize δ_spec q
          exact (δ_spec.mp hq).1
        · intro i hi
          have hi_data : i ∈ bar (s k) ∧ i ≤ s j := (ρ_spec i).mp hi
          rcases hi_data with ⟨hi_bar, hi_le⟩
          rcases I3 (I := I) (S := S) i j with hij | hij | hji
          · use s i; refine ⟨⟨?_, ?_⟩, ?_⟩
            · rw [ρ'_spec (s i)]
              constructor
              · have hsk : isN (s k) := I9.2 k hk
                have hi_bounds : 1 ≤ i ∧ i ≤ s k := (S2 (s k) hsk i).mp hi_bar
                apply (S2 (s k) hsk (s i)).mpr
                constructor
                · exact le_trans hi_bounds.1 (le_of_lt (I4 i))
                · have hj_bounds : 1 ≤ j ∧ j ≤ k := (S2 k hk j).mp hj
                  rcases I5 i j hij with hsi_eq_j | hsi_lt_j
                  · rw [hsi_eq_j]
                    exact le_trans hj_bounds.2 (le_of_lt (I4 k))
                  · exact le_trans (le_trans (le_of_lt hsi_lt_j) hj_bounds.2) (le_of_lt (I4 k))
              · rcases I5 i j hij with hsi_eq_j | hsi_lt_j
                · exact le_of_eq hsi_eq_j
                · exact le_of_lt hsi_lt_j
            · apply (δ_spec ⟪i, s i⟫).mpr
              constructor
              · apply (S5 ρ ρ' ⟪i, s i⟫).mpr
                refine ⟨i, s i, hi, ?_, rfl⟩
                apply (ρ'_spec (s i)).mpr
                constructor
                · have hsk : isN (s k) := I9.2 k hk
                  have hi_bounds : 1 ≤ i ∧ i ≤ s k := (S2 (s k) hsk i).mp hi_bar
                  apply (S2 (s k) hsk (s i)).mpr
                  constructor
                  · exact le_trans hi_bounds.1 (le_of_lt (I4 i))
                  · have hj_bounds : 1 ≤ j ∧ j ≤ k := (S2 k hk j).mp hj
                    rcases I5 i j hij with hsi_eq_j | hsi_lt_j
                    · rw [hsi_eq_j]
                      exact le_trans hj_bounds.2 (le_of_lt (I4 k))
                    · exact le_trans (le_trans (le_of_lt hsi_lt_j) hj_bounds.2) (le_of_lt (I4 k))
                · rcases I5 i j hij with hsi_eq_j | hsi_lt_j
                  · exact le_of_eq hsi_eq_j
                  · exact le_of_lt hsi_lt_j
              · left
                exact ⟨i, hi, hij, rfl⟩
            · intro y hy
              have hP := ((δ_spec ⟪i, y⟫).mp hy.2).2
              rcases hP with hmain | hspecial
              · rcases hmain with ⟨p, hpρ, hpltj, hp_eq⟩
                have hip : i = p :=
                  pair_left_injective (I := I) (S := S) i y p (s p) hp_eq
                have hysp : y = s p :=
                  pair_right_injective (I := I) (S := S) i y p (s p) hp_eq
                rw [hysp, ← hip]

              · rcases hspecial with hjcase | hsjcase
                · exfalso
                  have hij_eq : i = j :=
                    pair_left_injective (I := I) (S := S) i y j 1 hjcase
                  rw [hij_eq] at hij
                  exact I1 (I := I) (S := S) j hij

                · exfalso
                  have hi_sj : i = s j :=
                    pair_left_injective (I := I) (S := S) i y (s j) j hsjcase
                  have hi_lt_sj : i < s j := lt_trans hij (I4 j)
                  rw [hi_sj] at hi_lt_sj
                  exact I1 (I := I) (S := S) (s j) hi_lt_sj
          · refine ⟨1, ?_, ?_⟩
            · constructor
              · apply (ρ'_spec 1).mpr
                constructor
                · have hsk : isN (s k) := I9.2 k hk
                  apply (S2 (s k) hsk 1).mpr
                  constructor
                  · rfl
                  · exact (I10 (s k) 1 1 hsk).1
                · exact ((S2 k hk j).mp hj).1

              · apply (δ_spec ⟪i, 1⟫).mpr
                constructor
                · apply (S5 ρ ρ' ⟪i, 1⟫).mpr
                  refine ⟨i, 1, hi, ?_, rfl⟩
                  apply (ρ'_spec 1).mpr
                  constructor
                  · have hsk : isN (s k) := I9.2 k hk
                    apply (S2 (s k) hsk 1).mpr
                    constructor
                    · rfl
                    · exact (I10 (s k) 1 1 hsk).1
                  · exact ((S2 k hk j).mp hj).1
                · right
                  left
                  rw [hij]

            · intro y hy
              have hP := ((δ_spec ⟪i, y⟫).mp hy.2).2
              rcases hP with hmain | hspecial
              · rcases hmain with ⟨p, hpρ, hpltj, hp_eq⟩
                have hip : i = p :=
                  pair_left_injective (I := I) (S := S) i y p (s p) hp_eq
                exfalso
                have hbad : j < j := by
                  rw [← hip] at hpltj
                  rw [hij] at hpltj
                  exact hpltj
                exact I1 (I := I) (S := S) j hbad

              · rcases hspecial with hjcase | hsjcase
                · exact pair_right_injective (I := I) (S := S) i y j 1 hjcase

                · exfalso
                  have hi_sj : i = s j :=
                    pair_left_injective (I := I) (S := S) i y (s j) j hsjcase
                  have hjsj : j = s j := by
                    rw [← hij] at hi_sj ⊢
                    exact hi_sj
                  have hbad : j < j := by
                    simpa [← hjsj] using (I4 j)
                  exact I1 (I := I) (S := S) j hbad

          · have hi_eq_sj : i = s j := by
              rcases I5 j i hji with hsj_eq_i | hsj_lt_i
              · exact hsj_eq_i.symm
              · exfalso
                have hbad : s j < s j := lt_of_lt_of_le hsj_lt_i hi_le
                exact I1 (I := I) (S := S) (s j) hbad


            have hjρ' : j ∈ ρ' := by
              apply (ρ'_spec j).mpr
              constructor
              · have hsk : isN (s k) := I9.2 k hk
                apply (S2 (s k) hsk j).mpr
                constructor
                · exact ((S2 k hk j).mp hj).1
                · exact le_trans ((S2 k hk j).mp hj).2 (le_of_lt (I4 k))
              · rfl

            refine ⟨j, ?_, ?_⟩
            · constructor
              · exact hjρ'
              · apply (δ_spec ⟪i, j⟫).mpr
                constructor
                · apply (S5 ρ ρ' ⟪i, j⟫).mpr
                  exact ⟨i, j, hi, hjρ', rfl⟩
                · right
                  right
                  rw [hi_eq_sj]

            · intro y hy
              have hP := ((δ_spec ⟪i, y⟫).mp hy.2).2
              rcases hP with hmain | hspecial
              · rcases hmain with ⟨p, hpρ, hpltj, hp_eq⟩
                exfalso
                have hip : i = p :=
                  pair_left_injective (I := I) (S := S) i y p (s p) hp_eq
                have hiltj : i < j := by
                  rw [hip]
                  exact hpltj
                have hbad : j < j := lt_trans hji hiltj
                exact I1 (I := I) (S := S) j hbad

              · rcases hspecial with hjcase | hsjcase
                · exfalso
                  have hij_eq : i = j :=
                    pair_left_injective (I := I) (S := S) i y j 1 hjcase
                  have hbad : j < j := by
                    rw [hij_eq] at hji
                    exact hji
                  exact I1 (I := I) (S := S) j hbad

                · exact pair_right_injective (I := I) (S := S) i y (s j) j hsjcase

      have hjρ : j ∈ ρ := by
        apply (ρ_spec j).mpr
        constructor
        · have hsk : isN (s k) := I9.2 k hk
          apply (S2 (s k) hsk j).mpr
          constructor
          · exact ((S2 k hk j).mp hj).1
          · exact le_trans ((S2 k hk j).mp hj).2 (le_of_lt (I4 k))
        · exact le_of_lt (I4 j)

      have hρ_nonempty : isNonEmpty (I := I) ρ := by
        unfold isNonEmpty
        intro hnone
        exact hnone ⟨j, hjρ⟩

      have hnext : isNext (I := I) j (s j) (bar (s k)) := by
        unfold isNext
        constructor
        · have hsk : isN (s k) := I9.2 k hk
          apply (S2 (s k) hsk j).mpr
          constructor
          · exact ((S2 k hk j).mp hj).1
          · exact le_trans ((S2 k hk j).mp hj).2 (le_of_lt (I4 k))
        constructor
        · have hsk : isN (s k) := I9.2 k hk
          apply (S2 (s k) hsk (s j)).mpr
          constructor
          · exact le_trans ((S2 k hk j).mp hj).1 (le_of_lt (I4 j))
          · have hj_le_k : j ≤ k := ((S2 k hk j).mp hj).2
            rcases lt_or_eq_of_le hj_le_k with hj_lt_k | hj_eq_k
            · rcases I5 j k hj_lt_k with hsj_eq_k | hsj_lt_k
              · rw [hsj_eq_k]
                exact le_of_lt (I4 k)
              · exact le_trans (le_of_lt hsj_lt_k) (le_of_lt (I4 k))
            · rw [hj_eq_k]
        constructor
        · exact I4 j
        · intro x hx hjx
          rcases I5 j x hjx with hsj_eq_x | hsj_lt_x
          · exact le_of_eq hsj_eq_x
          · exact le_of_lt hsj_lt_x

      have hCeq : C ρ = s (C ρ') := by
        change
          C (InitialSegment (bar (s k)) (s j)) =
            s (C (InitialSegment (bar (s k)) j))
        exact C2' (I := I) (S := S) (bar (s k)) j (s j) hnext

      have hC_lt : C ρ' < C ρ := by
        rw [hCeq]
        exact I4 (C ρ')

      rcases C3' (I := I) δ ρ ρ' ⟨δ_isFunc, hρ_nonempty, hC_lt⟩
        with ⟨a, b, c, hab_ne, hacδ, hbcδ⟩

      have classify : ∀ x y : I, ⟪x, y⟫ ∈ δ →
      (∃ p : I, p ∈ ρ ∧ p < j ∧ x = p ∧ y = s p) ∨
      (x = j ∧ y = 1) ∨
      (x = s j ∧ y = j) := by
        intro x y hxy
        have hP := ((δ_spec ⟪x, y⟫).mp hxy).2
        rcases hP with hmain | hspecial
        · rcases hmain with ⟨p, hpρ, hp_lt, hp_eq⟩
          left
          refine ⟨p, hpρ, hp_lt, ?_, ?_⟩
          · exact pair_left_injective (I := I) (S := S) x y p (s p) hp_eq
          · exact pair_right_injective (I := I) (S := S) x y p (s p) hp_eq
        · rcases hspecial with hjcase | hsjcase
          · right
            left
            constructor
            · exact pair_left_injective (I := I) (S := S) x y j 1 hjcase
            · exact pair_right_injective (I := I) (S := S) x y j 1 hjcase
          · right
            right
            constructor
            · exact pair_left_injective (I := I) (S := S) x y (s j) j hsjcase
            · exact pair_right_injective (I := I) (S := S) x y (s j) j hsjcase

      have mem_bar_k_of_mem_ρ_lt_j : ∀ p : I, p ∈ ρ → p < j → p ∈ bar k := by
        intro p hpρ hp_lt_j
        apply (S2 k hk p).mpr
        constructor
        · have hp_bar_sk : p ∈ bar (s k) := ((ρ_spec p).mp hpρ).1
          have hsk : isN (s k) := I9.2 k hk
          exact ((S2 (s k) hsk p).mp hp_bar_sk).1
        · exact le_trans (le_of_lt hp_lt_j) ((S2 k hk j).mp hj).2

      have ha := classify a c hacδ
      have hb := classify b c hbcδ

      rcases ha with ha_main | ha_special
      · rcases ha_main with ⟨p, hpρ, hp_lt, ha_eq_p, hc_eq_sp⟩
        rcases hb with hb_main | hb_special
        · rcases hb_main with ⟨q, hqρ, hq_lt, hb_eq_q, hc_eq_sq⟩
          exfalso
          have hsp_sq : s p = s q := by
            rw [← hc_eq_sp, ← hc_eq_sq]
          have hpq : p = q := s_injective (I := I) (S := S) p q hsp_sq
          have hab : a = b := by
            rw [ha_eq_p, hb_eq_q, hpq]
          exact hab_ne hab
        · rcases hb_special with hb_j | hb_sj
          · rcases hb_j with ⟨hb_eq_j, hc_eq_one⟩
            exfalso
            have hsp_one : s p = 1 := by
              rw [← hc_eq_sp, hc_eq_one]
            have hp_bar_sk : p ∈ bar (s k) := ((ρ_spec p).mp hpρ).1
            have hsk : isN (s k) := I9.2 k hk
            have hp_one_le : 1 ≤ p := ((S2 (s k) hsk p).mp hp_bar_sk).1
            have hp_lt_one : p < 1 := by
              rw [← hsp_one]
              exact I4 p
            exact not_lt_of_ge hp_one_le hp_lt_one
          · rcases hb_sj with ⟨hb_eq_sj, hc_eq_j⟩
            refine ⟨p, ?_, ?_⟩
            · exact mem_bar_k_of_mem_ρ_lt_j p hpρ hp_lt
            · rw [← hc_eq_sp, hc_eq_j]

      · rcases ha_special with ha_j | ha_sj
        · rcases ha_j with ⟨ha_eq_j, hc_eq_one⟩
          rcases hb with hb_main | hb_special
          · rcases hb_main with ⟨q, hqρ, hq_lt, hb_eq_q, hc_eq_sq⟩
            exfalso
            have hsq_one : s q = 1 := by
              rw [← hc_eq_sq, hc_eq_one]
            have hq_bar_sk : q ∈ bar (s k) := ((ρ_spec q).mp hqρ).1
            have hsk : isN (s k) := I9.2 k hk
            have hq_one_le : 1 ≤ q := ((S2 (s k) hsk q).mp hq_bar_sk).1
            have hq_lt_one : q < 1 := by
              rw [← hsq_one]
              exact I4 q
            exact not_lt_of_ge hq_one_le hq_lt_one
          · rcases hb_special with hb_j | hb_sj
            · rcases hb_j with ⟨hb_eq_j, hc_eq_one'⟩
              exfalso
              have hab : a = b := by
                rw [ha_eq_j, hb_eq_j]
              exact hab_ne hab
            · rcases hb_sj with ⟨hb_eq_sj, hc_eq_j⟩
              exfalso
              have h1_eq_j : (1 : I) = j := by
                rw [← hc_eq_one, hc_eq_j]
              exact hjn1 h1_eq_j.symm

        · rcases ha_sj with ⟨ha_eq_sj, hc_eq_j⟩
          rcases hb with hb_main | hb_special
          · rcases hb_main with ⟨q, hqρ, hq_lt, hb_eq_q, hc_eq_sq⟩
            refine ⟨q, ?_, ?_⟩
            · exact mem_bar_k_of_mem_ρ_lt_j q hqρ hq_lt
            · rw [← hc_eq_sq, hc_eq_j]
          · rcases hb_special with hb_j | hb_sj
            · rcases hb_j with ⟨hb_eq_j, hc_eq_one⟩
              exfalso
              have hj_eq_one : j = (1 : I) := by
                rw [← hc_eq_j, hc_eq_one]
              exact hjn1 hj_eq_one
            · rcases hb_sj with ⟨hb_eq_sj, hc_eq_j'⟩
              exfalso
              have hab : a = b := by
                rw [ha_eq_sj, hb_eq_sj]
              exact hab_ne hab

    · intro i i' hi1 hi2 hi'1 hi'2
      apply s_injective (I := I) (S := S)
      rw [hi2, hi'2]

theorem least_element_principle_in_bar :
  ∀k:I, isN k → ∀σ:S, σ ⊆₀ bar k → isInhabited (I := I) σ →
  ∃ j : I, isFirst (I := I) j σ := by
  intro k hk σ hsub hinh
  classical
  by_contra hNo
  push_neg at hNo

  rcases hinh with ⟨w, hwσ⟩

  have hdesc : ∀ x : I, x ∈ σ → ∃ y : I, y ∈ σ ∧ y < x := by
    intro x hxσ
    have hx_not_first : ¬ isFirst (I := I) x σ := hNo x
    unfold isFirst at hx_not_first
    have hnot_all : ¬ ∀ y : I, y ∈ σ → x ≤ y := by
      intro hall
      exact hx_not_first ⟨hxσ, hall⟩
    push_neg at hnot_all
    rcases hnot_all with ⟨y, hyσ, hnotle⟩
    exact ⟨y, hyσ, hnotle⟩

  let ρ : S :=
    (S6 (fun q => ∃ p : I, p ∈ σ ∧ p ≤ q) (bar (s k))).1

  have ρ_spec :
      ∀ q : I, q ∈ ρ ↔
        q ∈ bar (s k) ∧ ∃ p : I, p ∈ σ ∧ p ≤ q := by
    intro q
    exact
      (S6
        (fun q => ∃ p : I, p ∈ σ ∧ p ≤ q)
        (bar (s k))).2 q
  let ρ' : S :=
    (S6 (fun q => ∃ p : I, p ∈ σ ∧ p ≤ q) (bar k)).1
  have ρ'_spec :
      ∀ q : I, q ∈ ρ' ↔
        q ∈ bar k ∧ ∃ p : I, p ∈ σ ∧ p ≤ q := by
    intro q
    exact (S6 (fun q => ∃ p : I, p ∈ σ ∧ p ≤ q) (bar k)).2 q
  let δ : S :=
    (S6 (fun r => ∃ q p : I, q ∈ ρ ∧ p ∈ ρ' ∧ r = ⟪q, p⟫ ∧ s p = q) (ρ * ρ')).1
  have δ_spec :
      ∀ r : I, r ∈ δ ↔
        r ∈ ρ * ρ' ∧
        ∃ q p : I,
          q ∈ ρ ∧ p ∈ ρ' ∧ r = ⟪q, p⟫ ∧ s p = q := by
    intro r
    exact (S6 (fun r => ∃ q p : I, q ∈ ρ ∧ p ∈ ρ' ∧ r = ⟪q, p⟫ ∧ s p = q) (ρ * ρ')).2 r
  have δ_isFunc : isFunc (I := I) δ ρ ρ' := by
    constructor
    · intro r hr
      exact ((δ_spec r).mp hr).1
    · intro q hqρ
      have hq_data := (ρ_spec q).mp hqρ
      rcases hq_data with ⟨hq_bar_sk, hq_upper⟩
      rcases hq_upper with ⟨r, hrσ, hr_le_q⟩
      have hq_ne_one : q ≠ 1 := by
        intro hq_eq_one
        have hr_bar_k : r ∈ bar k := hsub r hrσ
        have hr_bounds : 1 ≤ r ∧ r ≤ k := (S2 k hk r).mp hr_bar_k
        have hr_eq_one : r = 1 := by
          apply le_antisymm
          · rw [hq_eq_one] at hr_le_q
            exact hr_le_q
          · exact hr_bounds.1
        rcases hdesc r hrσ with ⟨t, htσ, ht_lt_r⟩
        have ht_bar_k : t ∈ bar k := hsub t htσ
        have ht_ge_one : 1 ≤ t := ((S2 k hk t).mp ht_bar_k).1
        have ht_lt_one : t < 1 := by
          rw [hr_eq_one] at ht_lt_r
          exact ht_lt_r
        exact not_lt_of_ge ht_ge_one ht_lt_one
      have hsk : isN (s k) := I9.2 k hk
      rcases predecessor_in_bar (I := I) (S := S) (s k) hsk q hq_bar_sk hq_ne_one with
        ⟨p, hp_pred, hp_unique⟩
      have hp_bar_sk : p ∈ bar (s k) := hp_pred.1
      have hspq : s p = q := hp_pred.2
      have hp_bar_k : p ∈ bar k := by
        apply (S2 k hk p).mpr
        constructor
        · exact ((S2 (s k) hsk p).mp hp_bar_sk).1
        · have hp_le_sk : p ≤ s k := ((S2 (s k) hsk p).mp hp_bar_sk).2
          apply le_of_not_gt
          intro hk_lt_p
          rcases I5 k p hk_lt_p with hsk_eq_p | hsk_lt_p
          · have hq_gt_sk : s k < q := by
              rw [← hspq, ← hsk_eq_p]
              exact I4 (s k)
            have hq_le_sk : q ≤ s k := ((S2 (s k) hsk q).mp hq_bar_sk).2
            exact not_lt_of_ge hq_le_sk hq_gt_sk
          · exact not_lt_of_ge hp_le_sk hsk_lt_p
      have hp_upper : ∃ r0 : I, r0 ∈ σ ∧ r0 ≤ p := by
        rcases lt_or_eq_of_le hr_le_q with hr_lt_q | hr_eq_q
        · refine ⟨r, hrσ, ?_⟩
          apply le_of_not_gt
          intro hp_lt_r
          rcases I5 p r hp_lt_r with hsp_eq_r | hsp_lt_r
          · have hq_eq_r : q = r := by
              rw [← hspq]
              exact hsp_eq_r
            rw [hq_eq_r] at hr_lt_q
            exact I1 (I := I) (S := S) r hr_lt_q
          · have hq_lt_q : q < q := by
              have : r < q := by exact gt_iff_lt.mp hr_lt_q
              have : s p < q := by exact I2 (CountingArithmetic.s S p) r q hsp_lt_r hr_lt_q
              rw [hspq] at this
              exact this
            exact I1 (I := I) (S := S) q hq_lt_q
        · rcases hdesc r hrσ with ⟨t, htσ, ht_lt_r⟩
          refine ⟨t, htσ, ?_⟩
          apply le_of_not_gt
          intro hp_lt_t
          rcases I5 p t hp_lt_t with hsp_eq_t | hsp_lt_t
          · have hq_eq_t : q = t := by
              rw [← hspq]
              exact hsp_eq_t
            have t_lt_q : t < q := by
              rw [hr_eq_q] at ht_lt_r
              exact ht_lt_r
            rw [← hq_eq_t] at t_lt_q
            exact I1 (I := I) (S := S) q t_lt_q
          · have t_lt_q : t < q := by
              rw [hr_eq_q] at ht_lt_r
              exact ht_lt_r
            have q_lt_q : q < q := by
              have : s p < r := by exact I2 (CountingArithmetic.s S p) t r hsp_lt_t ht_lt_r
              rw [hr_eq_q, hspq] at this
              exact this
            exact I1 (I := I) (S := S) q q_lt_q
      have hpρ' : p ∈ ρ' := by
        apply (ρ'_spec p).mpr
        exact ⟨hp_bar_k, hp_upper⟩
      refine ⟨p, ?_, ?_⟩
      · constructor
        · exact hpρ'
        · apply (δ_spec ⟪q, p⟫).mpr
          constructor
          · apply (S5 ρ ρ' ⟪q, p⟫).mpr
            exact ⟨q, p, hqρ, hpρ', rfl⟩
          · exact ⟨q, p, hqρ, hpρ', rfl, hspq⟩
      · intro y hy
        have hyρ' : y ∈ ρ' := hy.1
        have hqyδ : ⟪q, y⟫ ∈ δ := hy.2
        have hdata := ((δ_spec ⟪q, y⟫).mp hqyδ).2
        rcases hdata with ⟨q0, y0, hq0ρ, hy0ρ', hpair, hsy0⟩

        have hq_eq_q0 : q = q0 :=
          pair_left_injective (I := I) (S := S) q y q0 y0 hpair
        have hy_eq_y0 : y = y0 :=
          pair_right_injective (I := I) (S := S) q y q0 y0 hpair

        have hsyq : s y = q := by
          rw [hy_eq_y0, hq_eq_q0]
          exact hsy0

        apply s_injective (I := I) (S := S)
        rw [hsyq, hspq]
  have hρ_nonempty : isNonEmpty (I := I) ρ := by
    unfold isNonEmpty
    intro hnone
    apply hnone
    refine ⟨w, ?_⟩
    apply (ρ_spec w).mpr
    constructor
    · exact bar_subset_bar_succ (I := I) (S := S) k hk w (hsub w hwσ)
    · exact ⟨w, hwσ, le_rfl⟩
  have hkρ : k ∈ ρ := by
    apply (ρ_spec k).mpr
    constructor
    · exact bar_subset_bar_succ (I := I) (S := S) k hk k ((S2 k hk k).mpr ⟨(I10 k 1 1 hk).1, le_rfl⟩)
    · refine ⟨w, hwσ, ?_⟩
      exact ((S2 k hk w).mp (hsub w hwσ)).2
  have hskρ : s k ∈ ρ := by
    apply (ρ_spec (s k)).mpr
    constructor
    · have hsk : isN (s k) := I9.2 k hk
      apply (S2 (s k) hsk (s k)).mpr
      exact ⟨(I10 (s k) 1 1 hsk).1, le_rfl⟩
    · refine ⟨w, hwσ, ?_⟩
      exact le_trans ((S2 k hk w).mp (hsub w hwσ)).2 (le_of_lt (I4 k))
  have hnext : isNext (I := I) k (s k) ρ := by
    unfold isNext
    constructor
    · exact hkρ
    constructor
    · exact hskρ
    constructor
    · exact I4 k
    · intro x hxρ hk_lt_x
      rcases I5 k x hk_lt_x with hsk_eq_x | hsk_lt_x
      · exact le_of_eq hsk_eq_x
      · exact le_of_lt hsk_lt_x
  have hρ_top :
      InitialSegment ρ (s k) = ρ := by
    apply S1
    intro x
    constructor
    · intro hx
      exact ((InitialSegment_spec ρ (s k) x).mp hx).1
    · intro hxρ
      apply (InitialSegment_spec ρ (s k) x).mpr
      constructor
      · exact hxρ
      · have hx_bar_sk : x ∈ bar (s k) := ((ρ_spec x).mp hxρ).1
        have hsk : isN (s k) := I9.2 k hk
        exact ((S2 (s k) hsk x).mp hx_bar_sk).2
  have hρ'_eq :
      InitialSegment ρ k = ρ' := by
    apply S1
    intro x
    constructor
    · intro hx
      have hxdata := (InitialSegment_spec ρ k x).mp hx
      rcases hxdata with ⟨hxρ, hx_le_k⟩
      have hxρdata := (ρ_spec x).mp hxρ
      rcases hxρdata with ⟨hx_bar_sk, hx_upper⟩
      apply (ρ'_spec x).mpr
      constructor
      · apply (S2 k hk x).mpr
        constructor
        · have hsk : isN (s k) := I9.2 k hk
          exact ((S2 (s k) hsk x).mp hx_bar_sk).1
        · exact hx_le_k
      · exact hx_upper

    · intro hxρ'
      have hxρ'data := (ρ'_spec x).mp hxρ'
      rcases hxρ'data with ⟨hx_bar_k, hx_upper⟩
      apply (InitialSegment_spec ρ k x).mpr
      constructor
      · apply (ρ_spec x).mpr
        constructor
        · exact bar_subset_bar_succ (I := I) (S := S) k hk x hx_bar_k
        · exact hx_upper
      · exact ((S2 k hk x).mp hx_bar_k).2
  have hCeq :
      C (InitialSegment ρ (s k)) =
        s (C (InitialSegment ρ k)) := by
    exact C2' (I := I) (S := S) ρ k (s k) hnext
  have hCeq' : C ρ = s (C ρ') := by
    rw [hρ_top, hρ'_eq] at hCeq
    exact hCeq
  have hC_lt : C ρ' < C ρ := by
    rw [hCeq']
    exact I4 (C ρ')
  rcases C3' (I := I) δ ρ ρ' ⟨δ_isFunc, hρ_nonempty, hC_lt⟩ with
    ⟨a, b, c, hab_ne, hacδ, hbcδ⟩
  have ha_data := ((δ_spec ⟪a, c⟫).mp hacδ).2
  have hb_data := ((δ_spec ⟪b, c⟫).mp hbcδ).2
  rcases ha_data with ⟨qa, pa, hqaρ, hpaρ', ha_pair, hspa⟩
  rcases hb_data with ⟨qb, pb, hqbρ, hpbρ', hb_pair, hspb⟩
  have ha_eq_qa : a = qa :=
    pair_left_injective (I := I) (S := S) a c qa pa ha_pair
  have hc_eq_pa : c = pa :=
    pair_right_injective (I := I) (S := S) a c qa pa ha_pair
  have hb_eq_qb : b = qb :=
    pair_left_injective (I := I) (S := S) b c qb pb hb_pair
  have hc_eq_pb : c = pb :=
    pair_right_injective (I := I) (S := S) b c qb pb hb_pair
  have ha_eq_sc : a = s c := by
    calc
      a = qa := ha_eq_qa
      _ = s pa := hspa.symm
      _ = s c := by rw [hc_eq_pa]
  have hb_eq_sc : b = s c := by
    calc
      b = qb := hb_eq_qb
      _ = s pb := hspb.symm
      _ = s c := by rw [hc_eq_pb]
  have hab : a = b := by
    rw [ha_eq_sc, hb_eq_sc]
  exact hab_ne hab

theorem induction_in_N :
  ∀ P : I → Prop, P 1 → (∀ i : I, P i → P (s i)) →
  ∀ n : I, isN n → P n := by
  intro P h1 hs n hn
  classical
  by_contra hnP

  let Bad : S := (S6 (fun i => ¬ P i) (bar n)).1

  have Bad_spec :
      ∀ i : I, i ∈ Bad ↔ i ∈ bar n ∧ ¬ P i := by
    intro i
    exact (S6 (fun i => ¬ P i) (bar n)).2 i

  have hn_bar : n ∈ bar n := by
    apply (S2 n hn n).mpr
    constructor
    · exact (I10 n 1 1 hn).1
    · rfl

  have hBad_sub : Bad ⊆₀ bar n := by
    intro i hi
    exact ((Bad_spec i).mp hi).1

  have hBad_inhabited : isInhabited (I := I) Bad := by
    exact ⟨n, (Bad_spec n).mpr ⟨hn_bar, hnP⟩⟩

  rcases least_element_principle_in_bar
      (I := I) (S := S) n hn Bad hBad_sub hBad_inhabited with
    ⟨j, hjFirst⟩

  unfold isFirst at hjFirst

  have hjBad : j ∈ Bad := hjFirst.1
  have hjLeast : ∀ i : I, i ∈ Bad → j ≤ i := hjFirst.2

  have hj_data : j ∈ bar n ∧ ¬ P j := (Bad_spec j).mp hjBad
  have hj_bar : j ∈ bar n := hj_data.1
  have hj_notP : ¬ P j := hj_data.2

  by_cases hj_one : j = 1
  · rw [hj_one] at hj_notP
    exact hj_notP h1

  · rcases predecessor_in_bar
        (I := I) (S := S) n hn j hj_bar hj_one with
      ⟨i, hiPred, _hiUnique⟩

    have hi_bar : i ∈ bar n := hiPred.1
    have hsi : s i = j := hiPred.2
    have hiP : P i := by
      by_contra hi_notP
      have hiBad : i ∈ Bad := (Bad_spec i).mpr ⟨hi_bar, hi_notP⟩
      have hji : j ≤ i := hjLeast i hiBad
      have hij : i < j := by
        rw [← hsi]
        exact I4 i
      exact not_lt_of_ge hji hij
    have hjP : P j := by
      rw [← hsi]
      exact hs i hiP
    exact hj_notP hjP

theorem induction_in_N_standard :
  ∀ P : I → Prop,
    P 1 →
    (∀ i : I, isN i → P i → P (s i)) →
    ∀ n : I, isN n → P n := by
  intro P h1 hs n hn
  have hQ :
      (fun i : I => isN i ∧ P i) n := by
    exact induction_in_N
      (I := I) (S := S)
      (fun i : I => isN i ∧ P i)
      ⟨I9.1, h1⟩
      (by
        intro i hi
        exact ⟨I9.2 i hi.1, hs i hi.1 hi.2⟩)
      n hn
  exact hQ.2

theorem isN_of_mem_bar :
  ∀ n : I, isN n → ∀ i : I, i ∈ bar n → isN i := by
  intro n hn i hi
  classical
  by_contra hni

  let Bad : S := (S6 (fun x => ¬ isN x) (bar n)).1

  have Bad_spec :
      ∀ x : I, x ∈ Bad ↔ x ∈ bar n ∧ ¬ isN x := by
    intro x
    exact (S6 (fun x => ¬ isN x) (bar n)).2 x

  have hBad_sub : Bad ⊆₀ bar n := by
    intro x hx
    exact ((Bad_spec x).mp hx).1

  have hBad_inhabited : isInhabited (I := I) Bad := by
    exact ⟨i, (Bad_spec i).mpr ⟨hi, hni⟩⟩

  rcases least_element_principle_in_bar
      (I := I) (S := S) n hn Bad hBad_sub hBad_inhabited with
    ⟨j, hjFirst⟩

  unfold isFirst at hjFirst

  have hjBad : j ∈ Bad := hjFirst.1
  have hjLeast : ∀ x : I, x ∈ Bad → j ≤ x := hjFirst.2

  have hj_data : j ∈ bar n ∧ ¬ isN j := (Bad_spec j).mp hjBad
  have hj_bar : j ∈ bar n := hj_data.1
  have hj_notN : ¬ isN j := hj_data.2

  by_cases hj_one : j = 1
  · rw [hj_one] at hj_notN
    exact hj_notN I9.1

  · rcases predecessor_in_bar
        (I := I) (S := S) n hn j hj_bar hj_one with
      ⟨p, hpPred, _hpUnique⟩

    have hp_bar : p ∈ bar n := hpPred.1
    have hspj : s p = j := hpPred.2

    have hpN : isN p := by
      by_contra hp_notN
      have hpBad : p ∈ Bad := (Bad_spec p).mpr ⟨hp_bar, hp_notN⟩
      have hj_le_p : j ≤ p := hjLeast p hpBad
      have hp_lt_j : p < j := by
        rw [← hspj]
        exact I4 p
      exact not_lt_of_ge hj_le_p hp_lt_j

    have hjN : isN j := by
      rw [← hspj]
      exact I9.2 p hpN

    exact hj_notN hjN

theorem alt_proof_induction_in_N_standard :
  ∀ P : I → Prop,
    P 1 →
    (∀ i : I, isN i → P i → P (s i)) →
    ∀ n : I, isN n → P n := by
  intro P h1 hs n hn
  classical
  by_contra hnP

  let Bad : S := (S6 (fun i => ¬ P i) (bar n)).1

  have Bad_spec :
      ∀ i : I, i ∈ Bad ↔ i ∈ bar n ∧ ¬ P i := by
    intro i
    exact (S6 (fun i => ¬ P i) (bar n)).2 i

  have hn_bar : n ∈ bar n := by
    apply (S2 n hn n).mpr
    constructor
    · exact (I10 n 1 1 hn).1
    · rfl

  have hBad_sub : Bad ⊆₀ bar n := by
    intro i hi
    exact ((Bad_spec i).mp hi).1

  have hBad_inhabited : isInhabited (I := I) Bad := by
    exact ⟨n, (Bad_spec n).mpr ⟨hn_bar, hnP⟩⟩

  rcases least_element_principle_in_bar
      (I := I) (S := S) n hn Bad hBad_sub hBad_inhabited with
    ⟨j, hjFirst⟩

  unfold isFirst at hjFirst

  have hjBad : j ∈ Bad := hjFirst.1
  have hjLeast : ∀ i : I, i ∈ Bad → j ≤ i := hjFirst.2

  have hj_data : j ∈ bar n ∧ ¬ P j := (Bad_spec j).mp hjBad
  have hj_bar : j ∈ bar n := hj_data.1
  have hj_notP : ¬ P j := hj_data.2

  by_cases hj_one : j = 1
  · rw [hj_one] at hj_notP
    exact hj_notP h1

  · rcases predecessor_in_bar
        (I := I) (S := S) n hn j hj_bar hj_one with
      ⟨i, hiPred, _hiUnique⟩

    have hi_bar : i ∈ bar n := hiPred.1
    have hsi : s i = j := hiPred.2

    have hiN : isN i :=
      isN_of_mem_bar (I := I) (S := S) n hn i hi_bar

    have hiP : P i := by
      by_contra hi_notP
      have hiBad : i ∈ Bad := (Bad_spec i).mpr ⟨hi_bar, hi_notP⟩
      have hji : j ≤ i := hjLeast i hiBad
      have hij : i < j := by
        rw [← hsi]
        exact I4 i
      exact not_lt_of_ge hji hij

    have hjP : P j := by
      rw [← hsi]
      exact hs i hiN hiP

    exact hj_notP hjP


end Counting_Arithmetic
