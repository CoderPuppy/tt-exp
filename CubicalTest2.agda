{-# OPTIONS --cubical --type-in-type #-}
module CubicalTest2 where

open import Agda.Primitive.Cubical renaming (I to 𝕀; primIMin to _∧_; primIMax to _∨_; primINeg to ~_)
open import Agda.Builtin.Cubical.Path using (PathP)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

CubeSet : ℕ → Set
CubeSet zero = Set
CubeSet (succ n) = 𝕀 → CubeSet n

Cube : (n : ℕ) → CubeSet n → Set
Cube zero A = A
Cube (succ n) A = (i : 𝕀) → Cube n (A i)

Cube' : (n : ℕ) (A : CubeSet (succ n)) → Cube n (A i0) → Cube n (A i1) → Set
Cube' n A a0 a1 = PathP (λ i → Cube n (A i)) a0 a1
