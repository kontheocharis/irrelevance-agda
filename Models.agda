module Models where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit
open import Cubical.Data.Nat hiding (zero)

open import Theories

data ⊤ : Prop where
    tt : ⊤

data ⊥ : Prop where

propFunExt : ∀ {ℓ} {A : Prop} {B : A → Type ℓ} {f : (x : A) → B x} {g : (x : A) → B x}
  → ((x : A) → f x ≡ g x) → f ≡ g
propFunExt h i x = h x i

exfalso : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
exfalso ()

open ITT 
open ITT-sorts 
open ITT-ctors

-- MLTT model of ITT

-- Ignores irrelevance.

module MLTT-ITT {ℓ} {ℓ'} (m : MLTT {ℓ} {ℓ'}) where
  open MLTT

  i-sorts : ITT-sorts {lzero} {ℓ} {ℓ'}
  i-sorts .# = ⊤
  i-sorts .Ty = m .Ty
  i-sorts .Tm j A = m .Tm A
  [ i-sorts ] x = x tt
  (↑[ i-sorts ] x) x₁ = x₁
  [↑[ i-sorts ]]-id = refl
  ↑[[ i-sorts ]]-id = refl

  i-ctors : ITT-ctors i-sorts
  i-ctors .Π j A B = m .Π A B
  i-ctors .lam {z} f = m .lam f
  i-ctors .lam {ω} f = m .lam f
  i-ctors .app {z} = m .app 
  i-ctors .app {ω} = m .app
  i-ctors .lam-app {z} = m .lam-app
  i-ctors .lam-app {ω} = m .lam-app
  i-ctors .app-lam {z} = m .app-lam
  i-ctors .app-lam {ω} = m .app-lam
  i-ctors .U = m .U
  i-ctors .El = m .El
  i-ctors .Nat = m .Nat
  i-ctors .zero = m .zero
  i-ctors .succ = m .succ
  i-ctors .elim-Nat = m .elim-Nat
  i-ctors .elim-Nat-zero = m .elim-Nat-zero
  i-ctors .elim-Nat-succ = m .elim-Nat-succ

  i : ITT {lzero} {ℓ} {ℓ'}
  i .sorts = i-sorts
  i .ctors = i-ctors

-- LC model of ITT

-- Erases irrelevant stuff.

module LC-ITT {ℓ} (l : LC {ℓ}) where
  open LC

  i-sorts : ITT-sorts {lzero} {lzero} {ℓ}
  i-sorts .# = ⊥
  i-sorts .Ty = Unit
  i-sorts .Tm z tt = Unit*
  i-sorts .Tm ω tt = l .Λ
  [ i-sorts ] _ = tt*
  i-sorts .↑[_]_ = λ ()
  [↑[ i-sorts ]]-id = refl
  ↑[[ i-sorts ]]-id = propFunExt λ ()

  i-ctors : ITT-ctors i-sorts
  i-ctors .Π j A B = tt
  i-ctors .lam {z} f = f tt*
  i-ctors .lam {ω} f = l .lambda f
  i-ctors .app {z} f x = f
  i-ctors .app {ω} f x = l .apply f x
  i-ctors .lam-app {z} = refl
  i-ctors .lam-app {ω} = l .eta _
  i-ctors .app-lam {z} = refl
  i-ctors .app-lam {ω} = l .beta _ _
  i-ctors .U = tt
  i-ctors .El _ = tt
  i-ctors .Nat = tt
  i-ctors .zero = zeroΛ l
  i-ctors .succ x = succΛ l x
  i-ctors .elim-Nat X ze su n = recΛ l ze su n 
  i-ctors .elim-Nat-zero = recΛβ-zero l
  i-ctors .elim-Nat-succ = recΛβ-succ l

  i : ITT {lzero} {lzero} {ℓ}
  i .sorts = i-sorts
  i .ctors = i-ctors

-- Fam(Set) model of ITT
--
-- Since we need to produce a second-order model of ITT, we must work in the
-- internal language of Fam(Set). Luckily, this is (equivalent to) a presheaf
-- category, specifically the functor category I → Set where I is the 'walking
-- arrow'/interval category. Presheaf categories have an interpretation of
-- dependent type theory, so we can just use reuse Agda's. However, in this
-- category there is also a special object `P` which is (1, λ _ → 0) in
-- Fam(Set). Any two inhabitants of P are equal. If we take functions out of
-- this type `P → A`, it amounts to only looking at the 'set' component of A and
-- ignoring the 'family' component.

-- To that end, we interpret the relevant fragment of ITT using families of sets,
-- and the irrelevant fragment using empty families of sets.

module FamSet-ITT (P : Prop) where

  i-sorts : ITT-sorts {lzero} {lsuc (lsuc lzero)} {lsuc lzero}
  i-sorts .# = P
  i-sorts .Ty = Set1
  i-sorts .Tm z A = P → A
  i-sorts .Tm ω A = A
  [ i-sorts ] x = x
  (↑[ i-sorts ] x) x₁ = x₁ x
  [↑[ i-sorts ]]-id = refl
  ↑[[ i-sorts ]]-id = refl

  i-ctors : ITT-ctors i-sorts
  i-ctors .Π z A B = (a : P → A) → B a
  i-ctors .Π ω A B = (a : A) → B (λ _ → a)
  i-ctors .lam {z} f = f
  i-ctors .lam {ω} f = f
  i-ctors .app {z} x a = x a
  i-ctors .app {ω} x a = x a
  i-ctors .lam-app {z} = refl
  i-ctors .lam-app {ω} = refl
  i-ctors .app-lam {z} = refl
  i-ctors .app-lam {ω} = refl
  i-ctors .U = Set
  i-ctors .El X = Lift ((p : P) → X p)
  i-ctors .Nat = Lift ℕ 
  i-ctors .zero = lift ℕ.zero
  i-ctors .succ n = lift (suc (n .lower))
  i-ctors .elim-Nat X ze su (lift n) = elim
    {A = λ k → X (λ _ → lift k)}
    ze (λ k pk → su (lift k) pk) n 
  i-ctors .elim-Nat-zero = refl
  i-ctors .elim-Nat-succ = refl

  i : ITT {lzero} {lsuc (lsuc lzero)} {lsuc lzero}
  i .sorts = i-sorts
  i .ctors = i-ctors




