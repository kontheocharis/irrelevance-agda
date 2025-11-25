module Models where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit
open import Cubical.Data.Nat hiding (zero)

open import Theories
open import Gluing

data ⊤ : Prop where
    tt : ⊤

data ⊥ : Prop where

exfalso : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
exfalso ()

open ITT 
open ITT-sorts 
open ITT-ctors

-- MLTT model of ITT

-- Ignores irrelevance.

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

-- ITT model(1) of MLTT

module ITT-MLTT1 {ℓ} {ℓ'} (i : ITT {lzero} {ℓ} {ℓ'}) where
  open ITT
  open MLTT 
  open MLTT-sorts 
  open MLTT-ctors

  m-sorts : MLTT-sorts {ℓ} {ℓ'}
  m-sorts .Ty = i .Ty
  m-sorts .Tm A = i .Tm z A

  m-ctors : MLTT-ctors m-sorts
  m-ctors .Π = i .Π z -- z or ω doesn't matter here
  m-ctors .lam x = i .[_] (λ p → i .lam {z} (λ y → i .↑[_]_ p (x y)))
  m-ctors .app x y = {! i .[_] (λ p → app [x] ) !}
  m-ctors .lam-app = {!!}
  m-ctors .app-lam = {!!}
  m-ctors .U = {!!}
  m-ctors .El = {!!}
  m-ctors .Nat = {!!}
  m-ctors .zero = {!!}
  m-ctors .succ = {!!}
  m-ctors .elim-Nat = {!!}
  m-ctors .elim-Nat-zero = {!!}
  m-ctors .elim-Nat-succ = {!!}

  m : MLTT {ℓ} {ℓ'}
  m .sorts = m-sorts
  m .ctors = m-ctors



-- LC model of ITT

-- Erases irrelevant stuff.

module LC-ITT {ℓ} {ℓ'} (l : LC {ℓ'}) where
  open LC
  open ITT 
  open ITT-sorts 
  open ITT-ctors


  i-sorts : ITT-sorts {lzero} {ℓ} {ℓ'}
  i-sorts .# = ⊥
  i-sorts .Ty = Unit*
  i-sorts .Tm z tt* = Unit*
  i-sorts .Tm ω tt* = l .Λ
  [ i-sorts ] _ = tt*
  i-sorts .↑[_]_ = λ ()
  [↑[ i-sorts ]]-id = refl
  ↑[[ i-sorts ]]-id = propFunExt λ ()

  i-ctors : ITT-ctors i-sorts
  i-ctors .Π j A B = tt*
  i-ctors .lam {z} f = f tt*
  i-ctors .lam {ω} f = l .lambda f
  i-ctors .app {z} f x = f
  i-ctors .app {ω} f x = l .apply f x
  i-ctors .lam-app {z} = refl
  i-ctors .lam-app {ω} = l .eta _
  i-ctors .app-lam {z} = refl
  i-ctors .app-lam {ω} = l .beta _ _
  i-ctors .U = tt*
  i-ctors .El _ = tt*
  i-ctors .Nat = tt*
  i-ctors .zero = zeroΛ l
  i-ctors .succ x = succΛ l x
  i-ctors .elim-Nat X ze su n = recΛ l ze su n 
  i-ctors .elim-Nat-zero = recΛβ-zero l
  i-ctors .elim-Nat-succ = recΛβ-succ l

  i : ITT {lzero} {ℓ} {ℓ'}
  i .sorts = i-sorts
  i .ctors = i-ctors

-- Fam(Set) model of ITT
--
-- This is in a sense the "standard model" of ITT.
--
-- Since we need to produce a second-order model of ITT, we must work in the
-- internal language of Fam(Set). Luckily, this is (equivalent to) a presheaf
-- category, specifically the functor category I → Set where I is the 'walking
-- arrow'/interval category. Equivalently it is the arrow category Set^→.
-- Presheaf categories have an interpretation of dependent type theory, so we
-- can just use reuse Agda's. Additionally in this category there is also a
-- special object `P` which is (1, λ _ → 0) in Fam(Set). Any two inhabitants of
-- P are equal. If we take functions out of this `P → A`, it amounts to only
-- looking at the 'set' component of A and ignoring the 'family' component.

-- To that end, we interpret the relevant fragment of ITT using families of sets,
-- and the irrelevant fragment using empty families of sets.

module FamSet-ITT (P : Prop) where
  open ITT 
  open ITT-sorts 
  open ITT-ctors


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


-- Canonicity model of ITT

-- This is a displayed model, so we must work in a glued category. Specifically,
-- there is a functor Γ : I → Set from the syntax of I to closed terms. This is
-- usually what is used for canonicity. However, this is not sufficient for us.
-- Instead we want to build a functor Γ : I → Fam(Set), since we saw that the
-- standard model of ITT lives there. We send a type A to its set of irrelevant
-- closed terms a, and the family of relevant closed terms that project down to
-- a. We then extend this functor to Γ! : Psh I → Fam(Set) by the free
-- cocompletion. Gluing along this yields Fam(Set)/Γ!. Luckily, this is also a
-- presheaf topos (Carboni and Johnson 1995, Sterling and Harper 2020)

-- module canon-ITT (P : Prop) (Ψ : Prop) where
--   open ITT 
--   open ITT-sorts 
--   open ITT-ctors


--   -- here we have the syntax of ITT that restricts to the irrelevant fragment.
--   -- In other words, when P is true, then # is true in the syntax. (Sterling and
--   -- Harper, sec 3.3)
--   syn : Ψ → ITT {lzero} {lsuc (lsuc lzero)} {lsuc lzero}
--   res : (ψ : Ψ) → P true ≡ (syn ψ .sorts .#) true
--   res-prop : (ψ : Ψ) → P ≡ (syn ψ .sorts .#)

--   _⇒# : (ψ : Ψ) → P → syn ψ .sorts .#
--   (ψ ⇒#) p = (transport (res ψ) ⟦ p ⟧) .fact

--   #⇒_ : (ψ : Ψ) → syn ψ .sorts .# → P
--   (#⇒ ψ) p = (transport (sym (res ψ)) ⟦ p ⟧) .fact

--   -- We need to make a displayed model over the syntax
--   i-sorts : [ ITT-sorts {lzero} {lsuc (lsuc lzero)} {lsuc lzero} ∣ ψ ∈ Ψ ↪ syn ψ .sorts ]
--   i-sorts .fst .# = P
--   i-sorts .fst .Ty = G[ A ∈ (λ ψ → syn ψ .Ty) ] [ Set1 ∣ ψ ∈ Ψ ↪ syn ψ .Tm ω (A ψ) ]
--   i-sorts .fst .Tm ω A = A .snd .fst
--   i-sorts .fst .Tm z A
--     = G[ a ∈ (λ ψ → syn ψ .Tm z (A .fst ψ)) ]
--       [ (P → A .snd .fst) ∣ ψ ∈ Ψ ↪
--         (λ p → give ψ
--           (λ _ → syn ψ .Tm ω (A .fst ψ)) (A .snd)
--           (syn ψ .↑[_]_ ((ψ ⇒#) p) (a ψ))  ) ]
--   [ i-sorts .fst ] {A} x
--     = (λ ψ → syn ψ .[_] λ h → give' ψ (λ _ → syn ψ .Tm ω (A .fst ψ)) (A .snd) (x ((#⇒ ψ) h)))
--     , x
--     ,  λ ψ → propFunExt (λ p → {! !}) 
--     -- ,  λ ψ → {! propFunExt (λ p → sym (give-give' ψ (λ _ → syn ψ .Tm ω (A .fst ψ)) (A .snd) ?)) !}
--   (↑[ i-sorts .fst ] x) x₁ = x₁ .snd .fst x
--   [↑[ i-sorts .fst ]]-id = {! !}
--   ↑[[ i-sorts .fst ]]-id = refl
--   i-sorts .snd ψ i .# = (res-prop ψ) i 
--   i-sorts .snd ψ i .Ty = G-collapses ψ {(λ ψ → syn ψ .Ty)}
--                   {λ A → [ Set1 ∣ ψ ∈ Ψ ↪ syn ψ .Tm ω (A ψ) ]} {{ext-⋆}} i
--   i-sorts .snd ψ i .Tm ω A = {! A .snd!}
--   i-sorts .snd ψ i .Tm z A = {! !}
--   [ i-sorts .snd ψ i ] = {!!}
--   i-sorts .snd ψ i .↑[_]_ = {!!}
--   [↑[ i-sorts .snd ψ i ]]-id = {!!}
--   ↑[[ i-sorts .snd ψ i ]]-id = {!!}

--   i-ctors : [ ITT-ctors (* i-sorts) ∣ ψ ∈ Ψ ↪ *coe ψ ITT-ctors i-sorts (syn ψ .ctors)  ]
--   i-ctors .fst = {!!}
--   i-ctors .snd = {!!}

--   i : [ ITT {lzero} {lsuc (lsuc lzero)} {lsuc lzero} ∣ Ψ ↪ syn ]
--   i .fst .sorts = * i-sorts
--   i .fst .ctors = * i-ctors 
--   i .snd ψ i .sorts = (i-sorts ＠ ψ) i 
--   i .snd ψ i .ctors = {! !}


-- -- Code extraction model
-- -- ...


-- -- Category is Set/<id, Γ>
-- module code-extraction-correct-ITT (ϕΓ : Prop) (ϕid : Prop) where
--   open LC
--   open ITT 
--   open ITT-sorts 
--   open ITT-ctors


--   -- here we have the syntax of ITT that restricts to the irrelevant fragment.
--   -- In other words, when P is true, then # is true in the syntax. (Sterling and
--   -- Harper, sec 3.3)
--   postulate
--     disjoint : ϕΓ → ϕid → ⊥
--     l : ∀ {ℓ} → ϕΓ → LC {ℓ}

--   -- This is the code extraction model of ITT
--   li : ∀ {ℓ} {ℓ'} → ϕΓ → ITT {lzero} {ℓ} {ℓ'}
--   li p = LC-ITT.i (l p) 

--   -- We are gonna make a displayed model over this one
  
--   i-sorts : [ ITT-sorts {lzero} {lsuc (lsuc lzero)} {lsuc lzero} ∣ p ∈ ϕΓ ↪ li p .sorts ]
--   i-sorts .fst .# = ϕid
--   i-sorts .fst .Ty = [ Set1 ∣ p ∈ ϕΓ ↪ l p .Λ ]
--   i-sorts .fst .Tm z A = ϕid → A .fst
--   i-sorts .fst .Tm ω A = A .fst
--   [ i-sorts .fst ] x x₁ = x x₁
--   i-sorts .fst .↑[_]_ = λ z₁ z₂ → z₂ z₁
--   [↑[ i-sorts .fst ]]-id = refl
--   ↑[[ i-sorts .fst ]]-id = refl
--   i-sorts .snd p i .# = {! !}
--   i-sorts .snd p i .Ty = {!!}
--   i-sorts .snd p i .Tm = {!!}
--   [ i-sorts .snd p i ] = {!!}
--   i-sorts .snd p i .↑[_]_ = {!!}
--   [↑[ i-sorts .snd p i ]]-id = {!!}
--   ↑[[ i-sorts .snd p i ]]-id = {!!}

--   i-ctors : [ ITT-ctors (* i-sorts) ∣ p ∈ ϕΓ ↪ *coe p ITT-ctors i-sorts (li p .ctors)  ]
--   i-ctors .fst .Π z A B = G[ x ∈ (λ p → l p .Λ) ]
--     [ ((a : ϕid → A .fst) → (B a) .fst)
--       ∣ p ∈ ϕΓ ↪ (λ a → give p (λ p → l p .Λ) (B a) (x p)) ]
--       , λ p → G-collapses p 
--   i-ctors .fst .Π ω A B = G[ x ∈ (λ p → l p .Λ) ]
--     [ ((a : A .fst) → (B (λ _ → a)) .fst)
--       ∣ p ∈ ϕΓ ↪ (λ a → give p (λ p → l p .Λ) (B (λ _ → a)) (l p .apply (x p) (give' p (λ p → l p .Λ) A a))) ]
--       , λ p → G-collapses p 
--   i-ctors .fst .lam {z} {A} {X} f = ((λ p → give' p (λ p → l p .Λ)
--     (X (λ x → exfalso (disjoint p x)))
--     (f (λ x → exfalso (disjoint p x))))) ,  f , {! correct!}
--   i-ctors .fst .lam {ω} {A} {X} f = (λ p → l p .lambda (λ x →  give' p (λ p → l p .Λ)
--     (X (λ _ → give p (λ p → l p .Λ) A x))
--     (f (give p (λ p → l p .Λ) A x))))
--     ,  f , {! correct!}
--   i-ctors .fst .app {z} f x = f .snd .fst x
--   i-ctors .fst .app {ω} f x = f .snd .fst x
--   i-ctors .fst .lam-app {j = z} = {! ?!}
--   i-ctors .fst .lam-app {j = ω} = {! ?!}
--   i-ctors .fst .app-lam {z} = refl
--   i-ctors .fst .app-lam {ω} = refl
--   i-ctors .fst .U = [ Set ∣ p ∈ ϕΓ ↪ l p .Λ ] , {! correct!} 
--   i-ctors .fst .El X = (Lift ((p : ϕid) → X p .fst)) ,  λ p → {! correct!}
--   i-ctors .fst .Nat =  G[ n ∈ (λ p → l p .Λ) ] (ϕΓ ⋆ (Σ[ k ∈ ℕ ] (ϕid ⋆ (n ≡ (λ p → embed-nat (l p) k))))) , λ x → G-collapses x
--   i-ctors .fst .zero = (λ p → zeroΛ (l p)) , η ((0 , η refl))
--   i-ctors .fst .succ n = (λ p → succΛ (l p) (n .fst p))
--     , do
--       n' ← n .snd
--       η ((suc (n' .fst) , do n'' ← n' .snd ; η (propFunExt (λ p → cong (λ k → succΛ (l p) (k p)) n''))))
--   i-ctors .fst .elim-Nat P z' s' (n , nope p) = give p (λ p → l p .Λ) (P _)
--     (recΛ (l p) (give' p (λ p → l p .Λ) (P _) z')
--       (λ k pk → give' p (λ p → l p .Λ) (P _)
--         (s' ((λ p → k) , nope p) (give p (λ p → l p .Λ) (P _) pk)))
--       (n p))
--   i-ctors .fst .elim-Nat P z' s' (n , η (ℕ.zero , np)) = transport (λ i → P {! !} .fst) z' 
--   i-ctors .fst .elim-Nat P z' s' (n , η (suc n' , np)) = {! !}
--   i-ctors .fst .elim-Nat P z' s' (n , trivial p i) = {!!}
--   i-ctors .fst .elim-Nat-zero = {!!}
--   i-ctors .fst .elim-Nat-succ = {!!}
--   i-ctors .snd = {!!}

--   i : [ ITT {lzero} {lsuc (lsuc lzero)} {lsuc lzero} ∣ ϕΓ ↪ li ]
--   i .fst .sorts = * i-sorts
--   i .fst .ctors = * i-ctors 
--   i .snd ψ i .sorts = (i-sorts ＠ ψ) i 
--   i .snd ψ i .ctors = {! !}



--   module noninterference (f : i-sorts .fst .Tm ω (i-ctors .fst .Π z (i-ctors .fst .Nat) (λ _ → i-ctors .fst .Nat))) where

--     sem : (ϕΓ ⋆ ℕ) → (ϕΓ ⋆ ℕ)
--     sem n = do
--       let (fΛ , f , p) = f
--       n' ← n
--       let x = f λ p → (λ q → embed-nat (l q) n') , η (n' , η refl)
--       x' ← x .snd
--       η (x' .fst)

--     noninterference : ϕΓ ⋆ (Σ[ n ∈ ℕ ] (∀ p → f .fst p ≡ embed-nat (l p) n))
--     noninterference = do
--       let (fΛ , f , p) = f
--       let (x , xp) = f  λ q →  {! ? , ?!}
--       xp' ← xp
--       η ( xp' .fst , {! !})

  
