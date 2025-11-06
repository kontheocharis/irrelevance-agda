{-# OPTIONS --allow-unsolved-metas #-}
module Gluing where

open import Cubical.Foundations.Prelude renaming (_∙_ to trans)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Data.Unit
open import Data.Empty
open import Agda.Primitive
open import Relation.Binary.Reasoning.Syntax
import Agda.Builtin.Equality

private
  variable
    ℓ ℓ' : Level
    M N : Type ℓ
    P Q : Prop

propFunExt : {A : Prop} {B : A → Type ℓ} {f : (x : A) → B x} {g : (x : A) → B x}
  → ((x : A) → f x ≡ g x) → f ≡ g
propFunExt h i x = h x i

propFunExtP : {A : Prop} {B : A → I → Type ℓ'}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1}
  → ((x : A) → PathP (B x) (f x) (g x))
  → PathP (λ i → (x : A) → B x i) f g
propFunExtP p i x = p x i

case_to_of_ : {A : Type ℓ} (x : A) (P : A → Type ℓ') (f : (a : A) → P a) → P x
case_to_of_ x P f = f x
  
record _true (P : Prop) : Type where
  constructor ⟦_⟧
  field
    fact : P
open _true public

data _or_ (P Q : Prop) : Prop where
  inl : P → P or Q
  inr : Q → P or Q

open _true

data _⋆_ (P : Prop) (M : Type ℓ) : Type ℓ where
  nope : (p : P) → P ⋆ M
  η : M → P ⋆ M
  trivial : (p : P) {x : M} → nope p ≡ η x

⋆-collapses : (p : P) (y : P ⋆ M) → nope p ≡ y
⋆-collapses p (nope p) = refl
⋆-collapses p (η x) = trivial p
⋆-collapses p (trivial p {x = x} i) j = trivial p {x = x} (i ∧ j)

⋆→-trivial : P → (P ⋆ M) ≃ ⊤
⋆→-trivial p .fst x = tt
⋆→-trivial p .snd .equiv-proof tt = (nope p , refl) , λ (y , _) i → (⋆-collapses p y i) , refl

weaken : P ⋆ M → (Q or P) ⋆ M
weaken (nope p) = nope (inr p)
weaken (η x) = η x
weaken (trivial p {x} i) = trivial (inr p) {x} i

record _⋆-Modal_ (P : Prop) (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = P true × M} {B = P true} (λ (p , _) → p)

  collapses : P → isContr M
  collapses p = invIsEq prf ⟦ p ⟧ .snd
    ,  λ m →  λ i → retIsEq prf (⟦ p ⟧ , m) i .snd

  nope' : (p : P) → M
  nope' p = invIsEq prf ⟦ p ⟧ .snd

  trivial' : (p : P) {x : M} → nope' p ≡ x
  trivial' p {x = x} = collapses p .snd x

  iso-⋆ : Iso (P ⋆ M) M
  iso-⋆  = {!!}
  -- iso-⋆ .Iso.fun (nope p) = nope' p
  -- iso-⋆ .Iso.fun (η x) = x
  -- iso-⋆ .Iso.fun (trivial p {x = x} i) = trivial' p {x = x} i
  -- iso-⋆ .Iso.inv x = η x
  -- iso-⋆ .Iso.rightInv b = refl
  -- iso-⋆ .Iso.leftInv (nope p) = sym (⋆-collapses p (η (nope' p)))
  -- iso-⋆ .Iso.leftInv (η x) = refl
  -- iso-⋆ .Iso.leftInv (trivial p {x = x} i) j = {!!}

open _⋆-Modal_ public

record _→-Modal (P : Prop) (M : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    prf : isEquiv {A = M} {B = {{p : P}} → M} (λ x → x)

_→ᴰ_ : (P : Prop) → (P → Type ℓ) → Type ℓ
_→ᴰ_ P A = (p : P) → A p

ext : (A : Type ℓ) → (P : Prop) → ((p : P) → A) → Type ℓ
ext M P x = Σ[ a ∈ M ] ((p : P) → a ≡ x p)

[_∣_↪_] : (A : Type ℓ) → (P : Prop) → ((p : P) → A) → Type ℓ
[_∣_↪_] = ext

syntax ext M P (λ p → x) = [ M ∣ p ∈ P ↪ x ]

*_ : ∀ {x} → ext M P x → M
*_ = fst

_＠_ : ∀ {x} → (a : ext M P x) → (p : P) → * a ≡ (x p)
_＠_ a p = snd a p

*coe : ∀ {x} → (p : P) → (N : M → Type ℓ) → (s : ext M P x) → N (x p) → N (* s)
*coe p N s n = subst N (λ i → s .snd p (~ i)) n

give : ∀ {P} (p : P) A → (M : [ Type ℓ ∣ P ↪ A ]) → A p → M .fst
give p _ (M , l) a = transport (sym (l p)) a

give' : ∀ {P} (p : P) A → (M : [ Type ℓ ∣ P ↪ A ]) → M .fst → A p
give' p _ (M , l) a = transport (l p) a

give-give' : ∀ {P} (p : P) A (M : [ Type ℓ ∣ P ↪ A ]) (a : M .fst)
  → give p A M (give' p A M a) ≡ a
give-give' p A M a = transport⁻Transport (M .snd _) a

give'-give : ∀ {P} (p : P) A (M : [ Type ℓ ∣ P ↪ A ]) (a : A p)
  → give' p A M (give p A M a) ≡ a
give'-give p A M a = transportTransport⁻ (M .snd _) a

G : (A : P → (Type ℓ))
  → (B : (P →ᴰ A) → Type ℓ)
  → {{BP⋆ : ∀ {a : P →ᴰ A} → P ⋆-Modal (B a)}}
  → Type ℓ
G {P = P} A B = Σ[ a ∈ P →ᴰ A ] B a

G' : (A : P → (Type ℓ))
  → (B : (P →ᴰ A) → Type ℓ)
  → {{BP⋆ : ∀ {a : P →ᴰ A} → P ⋆-Modal (B a)}}
  → Type ℓ
G' {P = P} A B = Σ[ a ∈ P →ᴰ A ] B a

syntax G A (λ x → B) = G[ x ∈ A ] B

G-collapses : ∀ (p : P) {A : P → (Type ℓ)} {B : P →ᴰ A → Type ℓ}
  {{BP⋆ : ∀ {a : P →ᴰ A} → P ⋆-Modal (B a)}} → G[ a ∈ A ] B a ≡ A p
G-collapses p {A = A} {B = B} = {! !}

giveG : ∀ {A : P → (Type ℓ)} {B : P →ᴰ A → Type ℓ}
  {{BP⋆ : ∀ {a : P →ᴰ A} → P ⋆-Modal (B a)}}
  → (p : P) → A p → G[ x ∈ A ] B x
giveG {A = A} {B = B} p a = transport (sym (G-collapses p)) a

give'-beta : ∀ {A : P → (Type ℓ)} {B : P →ᴰ A → Type ℓ}
  {{BP⋆ : ∀ {a : P →ᴰ A} → P ⋆-Modal (B a)}} (p : P) (a : (p : P) → A p) (b : B a)
  → give' p A (G[ x ∈ A ] B x , λ p → G-collapses p) (a , b) ≡ a p
give'-beta p a b = {! !}
 
instance
  ext-⋆ : {x : P → M} → P ⋆-Modal [ M ∣ P ↪ x ]
  ext-⋆ = {!   !}

  ⋆-is-⋆-Modal : P ⋆-Modal (P ⋆ M)
  ⋆-is-⋆-Modal = {!!}

  or⋆-is-⋆-Modal : ∀ {Q} → P ⋆-Modal ((Q or P) ⋆ M)
  or⋆-is-⋆-Modal = {!!}

  ×-is-⋆-Modal : {A B : Type ℓ}
    → {{_ : P ⋆-Modal A}} → {{_ : P ⋆-Modal B}} → P ⋆-Modal (A × B)
  ×-is-⋆-Modal = {!!}

_>>=_ : P ⋆ M → (M → P ⋆ N) → P ⋆ N
nope p >>= f = nope p
η x >>= f = f x
_>>=_ {N = N} (trivial p {x = x} i) f = ⋆-collapses {M = N} p (f x) i

reconstruction : Iso (G[ x ∈ (λ _ → N) ] [ N ∣ P ↪ x ]) N
reconstruction .Iso.fun x = x .snd .fst
reconstruction .Iso.inv x = (λ p → x) , x , λ _ → refl
reconstruction .Iso.rightInv x = refl
reconstruction .Iso.leftInv (x , y , z) i = (λ p → z p i)
  , y , λ p j → z p (i ∧ j)

reconstruct : G[ x ∈ (λ _ → N) ] [ N ∣ P ↪ x ] → N
reconstruct = reconstruction .Iso.fun

deconstruct : N → G[ x ∈ (λ _ → N) ] [ N ∣ P ↪ x ]
deconstruct = reconstruction .Iso.inv

