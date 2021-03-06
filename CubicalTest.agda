{-# OPTIONS --cubical #-}

module CubicalTest where

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (I to ๐; primIMin to _โง_; primIMax to _โจ_; primINeg to ~_)
open import Agda.Builtin.Cubical.Path using (PathP)

-- ๐ : SSetโ
-- i0 : ๐
-- i1 : ๐
-- _โง_ : ๐ โ ๐ โ ๐
-- _โจ_ : ๐ โ ๐ โ ๐
-- ~_ : ๐ โ ๐
-- IsOne : ๐ โ Setฯ
-- itIsOne : IsOne i1
-- IsOne1 : (i : ๐) (j : ๐) โ IsOne i โ IsOne (i โจ j)
-- IsOne2 : (i : ๐) (j : ๐) โ IsOne j โ IsOne (i โจ j)
-- Partial : {a : Level} (ฯ : ๐) (A : Set a) โ SSet a
-- PartialP : {a : Level} (ฯ : ๐) (A : (o : IsOne ฯ) โ Set a) โ SSet a
-- isOneEmpty : {โ : Level} {A : Partial i0 (Set โ)} โ PartialP i0 A
-- primPOr : {โ : Level} (i j : ๐) (A : Partial (i โจ j) (Set โ)) (u : PartialP i (ฮป z โ A (IsOne1 i j z))) (v : PartialP j (ฮป z โ A (IsOne2 i j z))) โ PartialP (i โจ j) A
-- primComp : {โ : ๐ โ Level} (A : (i : ๐) โ Set (โ i)) {ฯ : I} (u : (i : ๐) โ Partial ฯ (A i)) (a : A i0) โ A i1
-- primTransp : {โ : ๐ โ Level} (A : (i : ๐) โ Set (โ i)) (ฯ : ๐) (a : A i0) โ A i1
-- primHComp : {โ : Level} {A : Set โ} {ฯ : I} (u : (i : ๐) โ Partial ฯ A) (a : A) โ A
-- PathP : {โ : Level} (A : ๐ โ Set โ) โ A i0 โ A i1 โ Set โ

-- data โ : Set where
--   zero : โ
--   succ : โ โ โ
-- {-# BUILTIN NATURAL โ #-}

-- data Sยน : Set where
--   base : Sยน
--   loop : PathP (ฮป _ โ Sยน) base base
--
-- data Inspect {โ : Level} (A : Set โ) : A โ Set โ where
--   inspect : (x : A) โ Inspect A x
--
-- data Unit : Set where
--   unit : Unit
--
-- w1 : PathP (ฮป _ โ Sยน) base base
-- w1 i = primHComp
--   (ฮป j โ ฮป{
--     (i = i0) โ base;
--     (i = i1) โ loop j
--   })
--   (loop i)
--
-- w2 : ๐ โ Sยน
-- w2 i = loop i
--
-- w3 : PathP (ฮป _ โ Sยน) base base
-- w3 i = w2 i

-- Cube' : {โ : Level} โ (n : โ) โ Set โ
-- Cube' 0 A = A
-- Cube' (succ n) A = ๐ โ Cube' n A

-- Cube' : (n : โ) โ Cube' n (ฮป _ โ Set) โ Set
-- Cube' n A = (v : Vec n ๐) โ A v
-- Cube : (n : โ) (A : Cube' (succ n) (ฮป _ โ Set)) (a0 : Cube' n (ฮป v โ A (i0 โท v))) (a1 : Cube' n (ฮป v โ A (i1 โท v))) โ Set
-- MkCube : (n : โ) (A : Cube' (succ n) (ฮป _ โ Set)) (a : Cube' (succ n) A) โ Cube n A (ฮป v โ a (i0 โท v)) (ฮป v โ a (i1 โท v))
