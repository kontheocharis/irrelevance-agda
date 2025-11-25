module Theories where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
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

private
  variable
    ℓ ℓ' ℓp ℓty ℓtm : Level

-- ITT

record ITT-sorts {ℓp} {ℓty} {ℓtm} : Type (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
  field
    # : Prop ℓp
    Ty : Type ℓty
    Tm : Mode → Ty → Type ℓtm

    -- Map to irrelevant
    [_] : ∀ {A} → (# → Tm ω A) → Tm z A
    ↑[_]_ : ∀ {A} → # → Tm z A → Tm ω A
    [↑[_]]-id : ∀ {A} {t : Tm z A} → [ ↑[_] t ] ≡ t
    ↑[[_]]-id : ∀ {A} {t# : # → Tm ω A} → ↑[_] [ t# ] ≡ t#

  coe : ∀ {A B} → A ≡ B → Tm i A → Tm i B
  coe {i = i} p a = transport ((λ k → Tm i (p k))) a
    
module _ (sorts : ITT-sorts {ℓp} {ℓty} {ℓtm}) where
  open ITT-sorts sorts
  
  private
    variable
      A B C : Ty
      A# B# C# : # → Ty
      X Y Z : Tm _ _ → Ty
      X# Y# Z# : (p : #) → Tm _ _ → Ty
      t u v : Tm _ _
      t# u# v# : (p : #) → Tm _ _
      f g h : (a : Tm _ _) → Tm _ _
      eq : _ ≡ _
      
  [_]* : Tm i A → Tm z A
  [_]* {i = z} t = t
  [_]* {i = ω} t = [ (λ _ → t) ]
      
  record ITT-ctors : Type (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
    field
      -- Pi types
      Π : (j : Mode) → (A : Ty) → (Tm z A → Ty) → Ty
      lam : ((a : Tm j A) → Tm ω (X [ a ]*)) → Tm ω (Π j A X)
      app : Tm ω (Π j A X) → (a : Tm j A) → Tm ω (X [ a ]*)

      -- Beta rules for irrelevant fragment
      lam-app : lam {j} (app t) ≡ t
      app-lam : app {j} (lam f) t ≡ f t

      -- Universe
      U : Ty
      El : Tm z U → Ty

      -- Natural numbers
      Nat : Ty
      zero : Tm ω Nat
      succ : Tm ω Nat → Tm ω Nat
      elim-Nat : (X : Tm z Nat → Ty)
        → (Tm ω (X [ zero ]*))
        → ((n : Tm ω Nat) → Tm ω (X [ n ]*) → Tm ω (X [ succ n ]*))
        → (n : Tm ω Nat) → Tm ω (X [ n ]*)

      -- Computation for elim-Nat
      elim-Nat-zero : ∀ {mz ms} → elim-Nat X mz ms zero ≡ mz
      elim-Nat-succ : ∀ {mz ms n} → elim-Nat X mz ms (succ n) ≡ ms n (elim-Nat X mz ms n)

    -- irrelevant fragment
    lamz : ((a : Tm j A) → Tm z (X [ a ]*)) → Tm z (Π j A X)
    lamz f = [ (λ p → lam (λ x → ↑[ p ] (f x)) ) ]

    lamz' : ((a : Tm z A) → Tm z (X a)) → Tm z (Π j A X)
    lamz' f = [ (λ p → lam (λ x → ↑[ p ] (f [ x ]*)) ) ]

    appz : Tm z (Π j A X) → (a : Tm j A) → Tm z (X [ a ]*)
    appz f x = [ (λ p → app (↑[ p ] f) x) ]

    appz' : Tm z (Π j A X) → (a : Tm z A) → Tm z (X a)
    appz' {j = z} f x = [ (λ p → app (↑[ p ] f) x) ]
    appz' {j = ω} {X = X} f x = [ (λ p → coe (cong X [↑[_]]-id) (app (↑[ p ] f) (↑[ p ] x) )) ]

    lamz-appz : lamz {j} (appz t) ≡ t
    lamz-appz {t = t} =
      (λ i → [ ( λ p → lam (λ x → ↑[[_]]-id {t# =  λ _ → app (↑[ p ] t) x} i p)) ])
      ∙ ( λ i → [ (λ p →  lam-app {t = ↑[ p ] t} i) ])
      ∙ [↑[_]]-id

    appz-lamz : appz {j} (lamz f) t ≡ f t
    appz-lamz {f = f} {t = t} =
      ( λ i → [ (λ p → app (↑[[_]]-id {t# =  λ _ → lam (λ x → ↑[ p ] f x)} i p) t ) ])
      ∙ ( λ i → [ (λ p → app-lam {f = λ x → ↑[ p ] f x} {t = t} i) ])
      ∙ [↑[_]]-id

    lamz-appz' : lamz' {X = X} {j = j} (appz' t) ≡ t
    lamz-appz' {j = z} {t = t} = lamz-appz
    lamz-appz' {X = X} {j = ω} {t = t} =
      (λ i → [ ( λ p → lam (λ x → ↑[[_]]-id {t# =  λ _ →  coe (cong X [↑[_]]-id) (app (↑[ p ] t) (↑[ p ] ([ x ]*)) ) } i p)) ])
      ∙ (λ i → [ (λ p → {!  !}) ])  -- UMMMM
      ∙ [↑[_]]-id

    appz-lamz' : appz' {j = j} {X = X} (lamz' f) t ≡ f t
    appz-lamz' {j = z} {X = X} {f = f} {t = t} = appz-lamz
    appz-lamz' {j = ω} {X = X} {f = f} {t = t} =
      (λ i → [ (λ p → coe (cong X [↑[_]]-id) ({!!})) ])
      ∙ {!!} -- Just usual cubical BS
      ∙ [↑[_]]-id

    zeroz : Tm z Nat
    zeroz = [ zero ]*

    succz : Tm z Nat → Tm z Nat
    succz n = [ (λ p → succ (↑[ p ] n)) ]

    elim-Natz : (X : Tm z Nat → Ty)
      → (Tm z (X zeroz))
      → ((n : Tm z Nat) → Tm z (X n) → Tm z (X (succz n)))
      → (n : Tm z Nat) → Tm z (X n)
    elim-Natz X ze su n = coe (cong X [↑[_]]-id)
      [ (λ p → elim-Nat X (↑[ p ] ze) (λ k pk → coe ( λ i → X [ (λ p → succ (↑[[_]]-id {t# = λ _ → k} i p)) ])
        (↑[ p ] (su [ k ]* [ pk ]*))) (↑[ p ] n)) ]

    -- Computation for elim-Nat
    elim-Nat-zeroz : ∀ {mz ms} → elim-Natz X mz ms zeroz ≡ mz
    elim-Nat-zeroz = {! !}

    elim-Nat-succz : ∀ {mz ms n} → elim-Natz X mz ms (succz n) ≡ ms n (elim-Natz X mz ms n)
    elim-Nat-succz = {! !}


record ITT {ℓp} {ℓty} {ℓtm} : Type (lsuc (ℓp ⊔ ℓty ⊔ ℓtm)) where
  field
    sorts : ITT-sorts {ℓp} {ℓty} {ℓtm}
  open ITT-sorts sorts public
  field
    ctors : ITT-ctors sorts
  open ITT-ctors ctors public

-- MLTT

record MLTT-sorts {ℓty} {ℓtm} : Type (lsuc (ℓty ⊔ ℓtm)) where
  field
    Ty : Type ℓty
    Tm : Ty → Type ℓtm

  coe : ∀ {A B} → A ≡ B → Tm A → Tm B
  coe p a = transport ((λ k → Tm (p k))) a
    
module _ (sorts : MLTT-sorts {ℓty} {ℓtm}) where
  open MLTT-sorts sorts
  
  private
    variable
      A B C : Ty
      X Y Z : Tm _ → Ty
      t u v : Tm _
      f g h : (a : Tm _) → Tm _
      eq : _ ≡ _
  
  record MLTT-ctors : Type (lsuc (ℓty ⊔ ℓtm)) where
    field
      -- Pi types
      Π : (A : Ty) → (Tm A → Ty) → Ty
      lam : ((a : Tm A) → Tm (X a)) → Tm (Π A X)
      app : Tm (Π A X) → (a : Tm A) → Tm (X a)

      -- Beta rules for irrelevant fragment
      lam-app : lam (app t) ≡ t
      app-lam : app (lam f) t ≡ f t

      -- Universe
      U : Ty
      El : Tm U → Ty

      -- Natural numbers
      Nat : Ty
      zero : Tm Nat
      succ : Tm Nat → Tm Nat
      elim-Nat : (X : Tm Nat → Ty)
        → (Tm (X zero))
        → ((n : Tm Nat) → Tm (X n) → Tm (X (succ n)))
        → (n : Tm Nat) → Tm (X n)

      -- Computation for elim-Nat
      elim-Nat-zero : ∀ {mz ms} → elim-Nat X mz ms zero ≡ mz
      elim-Nat-succ : ∀ {mz ms n} → elim-Nat X mz ms (succ n) ≡ ms n (elim-Nat X mz ms n)

record MLTT {ℓty} {ℓtm} : Type (lsuc (ℓty ⊔ ℓtm)) where
  field
    sorts : MLTT-sorts {ℓty} {ℓtm}
  open MLTT-sorts sorts public
  field
    ctors : MLTT-ctors sorts
  open MLTT-ctors ctors public


-- Untyped LC

record LC : Type (lsuc ℓ) where
  field
    Λ : Type ℓ
    lambda : (f : Λ → Λ) → Λ
    apply : Λ → Λ → Λ
    beta : ∀ f x → apply (lambda f) x ≡ f x
    eta : ∀ f → lambda (λ x → apply f x) ≡ f

  _$_ : Λ → Λ → Λ
  x $ y = apply x y

  infixl 5 _$_

  syntax lambda (λ x → t) = ƛ x ⇒ t
    
  zeroΛ : Λ
  zeroΛ = ƛ z ⇒ ƛ s ⇒ z

  succΛ : Λ → Λ
  succΛ n = ƛ z ⇒ ƛ s ⇒ (s $ n $ (n $ z $ s))

  id : Λ
  id = ƛ x ⇒ x

  recΛ : Λ → (Λ → Λ → Λ) → Λ → Λ
  recΛ zr su n = n $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk)

  recΛβ-zero : ∀ {zr su} → recΛ zr su zeroΛ ≡ zr
  recΛβ-zero {zr} {su} =
      recΛ zr su zeroΛ
    ≡⟨⟩
      ((ƛ z ⇒ ƛ s ⇒ z) $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk))
    ≡⟨ (λ i → (beta (λ z → ƛ s ⇒ z) zr i) $ (ƛ k ⇒ ƛ sk ⇒ su k sk)) ⟩
      ((ƛ s ⇒ zr) $ (ƛ k ⇒ ƛ sk ⇒ su k sk))
    ≡⟨ (λ i → (beta (λ s → zr) (ƛ k ⇒ ƛ sk ⇒ su k sk) i)) ⟩
      zr
    ∎

  recΛβ-succ : ∀ {zr su n} → recΛ zr su (succΛ n) ≡ su n (recΛ zr su n)
  recΛβ-succ {zr} {su} {n} =
      recΛ zr su (succΛ n)
    ≡⟨⟩
      ((ƛ z ⇒ ƛ s ⇒ (s $ n $ (n $ z $ s))) $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk))
    ≡⟨ (λ i → (beta (λ z → ƛ s ⇒ (s $ n $ (n $ z $ s))) zr i) $ (ƛ k ⇒ ƛ sk ⇒ su k sk)) ⟩
      ((ƛ s ⇒ (s $ n $ (n $ zr $ s))) $ (ƛ k ⇒ ƛ sk ⇒ su k sk))
    ≡⟨ beta _ _ ⟩
      ((ƛ k ⇒ ƛ sk ⇒ su k sk) $ n $ (n $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk)))
    ≡⟨ (λ i → beta (λ k → ƛ sk ⇒ su k sk) n i $ (n $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk))) ⟩
      ((ƛ sk ⇒ su n sk) $ (n $ zr $ (ƛ k ⇒ ƛ sk ⇒ su k sk)))
    ≡⟨ beta _ _ ⟩ 
      su n (recΛ zr su n)
    ∎

  embed-nat : ℕ → Λ
  embed-nat ℕ.zero = zeroΛ
  embed-nat (suc x) = succΛ (embed-nat x)
