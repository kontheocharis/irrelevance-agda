{-# OPTIONS --type-in-type #-}
module Playground where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat using (ℕ; suc)
  
{-# BUILTIN REWRITE _≡_ #-}

-- Mode is either 0 (irrelevant) or ω (relevant)

data Mode : Set where
  z : Mode
  ω : Mode

opaque
  _*_ : Mode → Mode → Mode
  j * ω = j
  ω * j = j
  z * j = z

private
  variable
    i j : Mode
    
opaque
  unfolding _*_

  j*ω : j * ω ≡ j
  j*ω {z} = refl
  j*ω {ω} = refl

  ω*j : ω * j ≡ j
  ω*j {z} = refl
  ω*j {ω} = refl

  z*j : z * j ≡ z
  z*j {z} = refl
  z*j {ω} = refl

  j*z : j * z ≡ z
  j*z {z} = refl
  j*z {ω} = refl

-- Better definitional computation for _*_
{-# REWRITE j*ω ω*j z*j j*z #-}

postulate
  # : Prop
  Ty : Set
  Tm : Mode → Ty → Set

variable
  A B C : Ty
  p : #
  A# B# C# : # → Ty
  X Y Z : Tm _ _ → Ty
  X# Y# Z# : (p : #) → Tm _ _ → Ty
  t u v : Tm _ _
  t# u# v# : (p : #) → Tm _ _
  f g h : (a : Tm _ _) → Tm _ _

postulate
  [_] : (# → Tm ω A) → Tm z A
  ↑[_]_ : # → Tm z A → Tm ω A
  [↑[_]]-id : [ ↑[_] t ] ≡ t
  ↑[[_]]-id : ↑[ p ] [ t# ] ≡ t# p

  {-# REWRITE [↑[_]]-id ↑[[_]]-id #-}

[_]* : Tm i A → Tm z A
[_]* {i = z} t = t
[_]* {i = ω} t = [ (λ _ → t) ]
      
postulate
  Π : (j : Mode) → (A : Ty) → (Tm z A → Ty) → Ty
  lam : ((a : Tm j A) → Tm ω (X [ a ]*)) → Tm ω (Π j A X)
  app : Tm ω (Π j A X) → (a : Tm j A) → Tm ω (X [ a ]*)
  lam-app : lam {j} (app t) ≡ t
  app-lam : app {j} (lam f) t ≡ f t
  {-# REWRITE lam-app app-lam #-}

postulate
  U : Ty
  El : Tm z U → Ty
  code : Ty → Tm z U
  El-code : El (code A) ≡ A
  code-El : code (El t) ≡ t
  {-# REWRITE El-code code-El #-}


postulate
  Nat : Ty
  zero : Tm ω Nat
  succ : Tm ω Nat → Tm ω Nat
  elim-Nat : (X : Tm z Nat → Ty)
    → (Tm ω (X [ zero ]*))
    → ((n : Tm ω Nat) → Tm ω (X [ n ]*) → Tm ω (X [ succ n ]*))
    → (n : Tm ω Nat) → Tm ω (X [ n ]*)
  elim-Nat-zero : ∀ {mz ms} → elim-Nat X mz ms zero ≡ mz
  elim-Nat-succ : ∀ {mz ms n} → elim-Nat X mz ms (succ n) ≡ ms n (elim-Nat X mz ms n)
  {-# REWRITE elim-Nat-zero elim-Nat-succ #-}


-- irrelevant fragment
lamz : ((a : Tm z A) → Tm z (X a)) → Tm z (Π j A X)
lamz f = [ (λ p → lam (λ x → ↑[ p ] (f [ x ]*)) ) ]

appz : Tm z (Π j A X) → (a : Tm z A) → Tm z (X a)
appz {j = z} f x = [ (λ p → app (↑[ p ] f) x) ]
appz {j = ω} {X = X} f x = [ (λ p → app (↑[ p ] f) (↑[ p ] x)) ]

lamz-appz : lamz {X = X} {j = j} (appz t) ≡ t
lamz-appz {j = z} = refl
lamz-appz {j = ω} = refl

appz-lamz : appz {j = j} {X = X} (lamz f) t ≡ f t
appz-lamz {j = z} = refl
appz-lamz {j = ω} = refl

zeroz : Tm z Nat
zeroz = [ zero ]*

succz : Tm z Nat → Tm z Nat
succz n = [ (λ p → succ (↑[ p ] n)) ]

elim-Natz : (X : Tm z Nat → Ty)
  → (Tm z (X zeroz))
  → ((n : Tm z Nat) → Tm z (X n) → Tm z (X (succz n)))
  → (n : Tm z Nat) → Tm z (X n)
elim-Natz X ze su n = 
  [ (λ p → elim-Nat X (↑[ p ] ze) ( λ k pk → ↑[ p ] (su [ k ]* [ pk ]*)) (↑[ p ] n)) ]

elim-Nat-zeroz : ∀ {mz ms} → elim-Natz X mz ms zeroz ≡ mz
elim-Nat-zeroz = refl

elim-Nat-succz : ∀ {mz ms n} → elim-Natz X mz ms (succz n) ≡ ms n (elim-Natz X mz ms n)
elim-Nat-succz = {!!}
-- not sure why rewriting fails here but the goal clearly reduces

-- Vectors
postulate
  Vect : Tm z U → Tm z Nat → Ty
  nil : ∀ {t : Tm z U} → Tm ω (Vect t zeroz)
  cons : ∀ {t : Tm z U} {n : Tm z Nat} → Tm ω (El t) → Tm ω (Vect t n) → Tm ω (Vect t (succz n))

nilz :  ∀ {t : Tm z U} → Tm z (Vect t zeroz)
nilz = [ nil ]*

consz : ∀ {t : Tm z U} {n : Tm z Nat} → Tm z (El t) → Tm z (Vect t n) → Tm z (Vect t (succz n))
consz x xs = [ (λ p → cons (↑[ p ] x) (↑[ p ] xs)) ]

postulate
  elim-Vect : ∀ {t} → (X : (n : Tm z Nat) → Tm z (Vect t n) → Ty)
    → Tm ω (X zeroz nilz)
    → (∀ (n : Tm z Nat)
      → (x : Tm ω (El t))
      → (xs : Tm ω (Vect t n))
      → Tm ω (X n [ xs ]*)
      → Tm ω (X (succz n) (consz [ x ]* [ xs ]*)))
    → {n : Tm z Nat} → (v : Tm ω (Vect t n)) → Tm ω (X n [ v ]*)

  elim-Vect-nil : ∀ {t X ni co} → elim-Vect {t} X ni co nil ≡ ni
  elim-Vect-cons : ∀ {t X ni co n x xs}
    → elim-Vect {t} X ni co (cons {n = n} x xs) ≡ co n x xs (elim-Vect {t} X ni co xs)
  {-# REWRITE elim-Vect-nil elim-Vect-cons #-}

elim-Vectz : ∀ {t} → (X : (n : Tm z Nat) → Tm z (Vect t n) → Ty)
  → Tm z (X zeroz nilz)
  → (∀ (n : Tm z Nat)
    → (x : Tm z (El t))
    → (xs : Tm z (Vect t n))
    → Tm z (X n xs)
    → Tm z (X (succz n) (consz x xs)))
  → {n : Tm z Nat} → (v : Tm z (Vect t n)) → Tm z (X n v)
elim-Vectz X ni co v =
  [ (λ p → elim-Vect X (↑[ p ] ni)
          (λ n x xs pxs → ↑[ p ] (co _ [ x ]* [ xs ]* [ pxs ]*))
          (↑[ p ] v) ) ]

elim-Vect-nilz : ∀ {t X ni co} → elim-Vectz {t} X ni co nilz ≡ ni
elim-Vect-nilz = refl

elim-Vect-consz : ∀ {t X ni co n x xs}
    → elim-Vectz {t} X ni co (consz {n = n} x xs) ≡ co n x xs (elim-Vectz {t} X ni co xs)
elim-Vect-consz = {! !} -- same again


-- Implementation notes:


-- First thing to note is that instead of deriving the irrelevant
-- fragment, we can instead add it as a primitive, including equations
-- for the actions of [_] and ↑_.
--
-- As a result, [_] and ↑_ will commute with everything in the syntax,
-- and the only time we see them is when they are applied to variables.

-- Normal form analysis:
--
-- We have relevant and irrelevant normal forms, which look basically identical
-- in the simple setup, with the exception of universes which only exist in the
-- irrelevant phase.
--
-- For irrelevant neutrals, we have an extra form [_] for application heads.
-- For relevant neutrals, we have an extra form ↑_ for application heads.
-- These two coercions do not appear anywhere else in the normal forms.
--
-- In an implementation we can share a single data structure for the two forms
-- (like in 2LTT).

-- Irrelevance marker in contexts:

-- The SOGAT above will create a structural context extension _▷#.
-- I will call the resulting representable sort #∈ : Con → Set.
--
-- As part of this definition, we get the property
-- Sub Γ Δ × #∈ Γ ≃ Sub Γ (Δ ▷#)
--
-- Also note that #∈ Γ is a proposition, furthermore it is a decidable
-- proposition.
--
-- In an implementation of elaboration to this core language, it suffices to
-- have a boolean flag in the context to remember whether it is an irrelevant
-- context or not. This way it doesn't mess with the deBrujin indices/levels of
-- actual variables. As a result, we get free weakening/strengthening by # in
-- syntax *and* values. Relevant and irrelevant bindings can share deBrujin
-- indices/levels. Besides the types of each binding, the context must now
-- record the mode of each binding as well.

-- Surface language
--
-- For the input to elaboration, our presyntax can look exactly like the usual
-- surface language for dependent type theory, with the addition of 0/ω modes
-- for binder types (Π, Σ) and on let bindings. The rest can be inferred; in
-- particular, when we elaborate variables, we can insert [_] or ↑_ if needed.

-- Metavariable handling
--
-- An example metavariable spine might now look like
--
-- ?m p x y [z] (↑w)
--
-- where p is an additional boolean flag denoting if this context is irrelevant.
--
-- If p is true, then we can invert [z] with ↑z' and ↑w with [w'].
--
-- If p is false, then we cannot invert [z] because writing ↑z' is only
-- valid if the context is irrelevant. But we can still invert ↑w with [w'].
--
-- Sometimes, we will get problems that look like
--
-- [?m sp] =? t
--   or
-- ↑(?m sp) =? t
--
-- 1. In the former case, we can reduce it to
--
-- ?m sp =? ↑t
--
-- only if p is true in the context (in other words, if it appears in sp).]
-- If p is not true, then we can try to create a new meta ?m' sp', solve it with
-- [?m sp] then try to attack ?m' sp' =? t.
--
-- 2. In the latter case, we can always reduce it to
--
-- ?m sp =? [t]

