{-# OPTIONS --cubical #-}

module CubicalTest where

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (I to 𝕀; primIMin to _∧_; primIMax to _∨_; primINeg to ~_)
open import Agda.Builtin.Cubical.Path using (PathP)

-- 𝕀 : SSet₀
-- i0 : 𝕀
-- i1 : 𝕀
-- _∧_ : 𝕀 → 𝕀 → 𝕀
-- _∨_ : 𝕀 → 𝕀 → 𝕀
-- ~_ : 𝕀 → 𝕀
-- IsOne : 𝕀 → Setω
-- itIsOne : IsOne i1
-- IsOne1 : (i : 𝕀) (j : 𝕀) → IsOne i → IsOne (i ∨ j)
-- IsOne2 : (i : 𝕀) (j : 𝕀) → IsOne j → IsOne (i ∨ j)
-- Partial : {a : Level} (φ : 𝕀) (A : Set a) → SSet a
-- PartialP : {a : Level} (φ : 𝕀) (A : (o : IsOne φ) → Set a) → SSet a
-- isOneEmpty : {ℓ : Level} {A : Partial i0 (Set ℓ)} → PartialP i0 A
-- primPOr : {ℓ : Level} (i j : 𝕀) (A : Partial (i ∨ j) (Set ℓ)) (u : PartialP i (λ z → A (IsOne1 i j z))) (v : PartialP j (λ z → A (IsOne2 i j z))) → PartialP (i ∨ j) A
-- primComp : {ℓ : 𝕀 → Level} (A : (i : 𝕀) → Set (ℓ i)) {φ : I} (u : (i : 𝕀) → Partial φ (A i)) (a : A i0) → A i1
-- primTransp : {ℓ : 𝕀 → Level} (A : (i : 𝕀) → Set (ℓ i)) (φ : 𝕀) (a : A i0) → A i1
-- primHComp : {ℓ : Level} {A : Set ℓ} {φ : I} (u : (i : 𝕀) → Partial φ A) (a : A) → A
-- PathP : {ℓ : Level} (A : 𝕀 → Set ℓ) → A i0 → A i1 → Set ℓ

-- data ℕ : Set where
--   zero : ℕ
--   succ : ℕ → ℕ
-- {-# BUILTIN NATURAL ℕ #-}

data S¹ : Set where
  base : S¹
  loop : PathP (λ _ → S¹) base base

data Inspect {ℓ : Level} (A : Set ℓ) : A → Set ℓ where
  inspect : (x : A) → Inspect A x

data Unit : Set where
  unit : Unit

w1 : PathP (λ _ → S¹) base base
w1 i = primHComp
  (λ j → λ{
    (i = i0) → base;
    (i = i1) → loop j
  })
  (loop i)

w2 : 𝕀 → S¹
w2 i = loop i

w3 : PathP (λ _ → S¹) base base
w3 i = w2 i

-- Cube' : {ℓ : Level} → (n : ℕ) → Set ℓ
-- Cube' 0 A = A
-- Cube' (succ n) A = 𝕀 → Cube' n A

-- Cube' : (n : ℕ) → Cube' n (λ _ → Set) → Set
-- Cube' n A = (v : Vec n 𝕀) → A v
-- Cube : (n : ℕ) (A : Cube' (succ n) (λ _ → Set)) (a0 : Cube' n (λ v → A (i0 ∷ v))) (a1 : Cube' n (λ v → A (i1 ∷ v))) → Set
-- MkCube : (n : ℕ) (A : Cube' (succ n) (λ _ → Set)) (a : Cube' (succ n) A) → Cube n A (λ v → a (i0 ∷ v)) (λ v → a (i1 ∷ v))
