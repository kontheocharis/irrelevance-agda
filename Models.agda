module Models where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit

open import Theories

data ⊤ : Prop where
    tt : ⊤

data ⊥ : Prop where

propFunExt : ∀ {ℓ} {A : Prop} {B : A → Type ℓ} {f : (x : A) → B x} {g : (x : A) → B x}
  → ((x : A) → f x ≡ g x) → f ≡ g
propFunExt h i x = h x i

exfalso : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
exfalso ()

-- MLTT model of ITT

module MLTT-ITT {ℓ} {ℓ'} (m : MLTT {ℓ} {ℓ'}) where
  open MLTT
  open ITT 
  open ITT-sorts 
  open ITT-ctors

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

module LC-ITT {ℓ} (l : LC {ℓ}) where
  open LC
  open ITT 
  open ITT-sorts 
  open ITT-ctors

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
