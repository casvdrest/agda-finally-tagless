{-# OPTIONS --overlapping-instances #-}
module Experiment.PolymorphicDeBruijn where

open import Data.Vec  using (Vec ; _∷_ ; [] ; lookup)
open import Data.Fin  using (Fin ; suc ; zero)
open import Data.List using (List ; _∷_ ; [] ; [_]) renaming (length to size)
open import Data.Nat
open import Data.Bool 
open import Data.Product 
open import Data.String

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All

open import Data.List.Relation.Binary.Sublist.Propositional renaming (lookup to extend)

import Relation.Binary.PropositionalEquality as P

open import Level renaming (suc to sucL ; zero to zeroL)

module DB where

TyCtx = List String

data Type (Δ : TyCtx) : Set where
  ∀[_⇒_] : (a : String) → Type (a ∷ Δ) → Type Δ 
  _↦_    : (s t : Type Δ) → Type Δ
  #_     : (a : String) → ⦃ a ∈ Δ ⦄ → Type Δ
  nat    : Type Δ 

TEnv : (Δ : TyCtx) → Set
TEnv Δ = Vec (Type []) (size Δ)

instance ∈-here : ∀ {A : Set} {xs : List A} {x} → x ∈ x ∷ xs
∈-here = here P.refl

instance ∈-there : ∀ {A : Set} {xs : List A} {x y} → ⦃ x ∈ xs ⦄ → x ∈ y ∷ xs
∈-there ⦃ w ⦄ = there w

Ctx : TyCtx → Set 
Ctx Δ = List (String × Type Δ)

embed : ∀ {Δ Δ′} → Δ ⊆ Δ′ → Type Δ → Type Δ′ 
embed Δ⊆Δ′ ∀[ a ⇒ t ]   = ∀[ a ⇒ embed (P.refl ∷ Δ⊆Δ′) t ]
embed Δ⊆Δ′ (s ↦ t)      = embed Δ⊆Δ′ s ↦ embed Δ⊆Δ′ t
embed Δ⊆Δ′ (#_ a ⦃ l ⦄) = #_ a ⦃ extend Δ⊆Δ′ l ⦄
embed Δ⊆Δ′ nat          = nat

[]⊆Δ : ∀ {Δ : TyCtx} → [] ⊆ Δ
[]⊆Δ {[]}    = []
[]⊆Δ {x ∷ Δ} = x ∷ʳ []⊆Δ

⟪_⟫ : ∀ {Δ a} → Ctx Δ → Ctx (a ∷ Δ)
⟪ [] ⟫          = []
⟪ (x , t) ∷ Γ ⟫ = (x , embed (_ ∷ʳ ⊆-refl) t) ∷ ⟪ Γ ⟫

extr : ∀ {Δ Δ′}
       → (∀ {a : String} → a ∈ Δ → a ∈ Δ′)
       → ∀ {a b : String} → a ∈ b ∷ Δ → a ∈ b ∷ Δ′
extr ρ (here P.refl) = here P.refl
extr ρ (there x)   = there (ρ x)

rename : ∀ {Δ Δ′}
         → (∀ {a} → a ∈ Δ → a ∈ Δ′)
         → Type Δ → Type Δ′
rename ρ ∀[ b ⇒ t ] = ∀[ b ⇒ rename (extr ρ) t ]
rename ρ (s ↦ t) = rename ρ s ↦ rename ρ t
rename ρ (#_ a ⦃ l ⦄ ) = #_ a ⦃ ρ l ⦄
rename ρ nat = nat

exts : ∀ {Δ Δ′}
       → (∀ {a} → a ∈ Δ → Type Δ′)
       → ∀ {a b} → a ∈ b ∷ Δ → Type (b ∷ Δ′)
exts σ {b = b} (here P.refl) = # b
exts σ         (there x) = rename there (σ x)

subst : ∀ {Δ Δ′}
        → (∀ {a} → a ∈ Δ → Type Δ′) 
        → Type Δ → Type Δ′
subst σ ∀[ b ⇒ t ] = ∀[ b ⇒ subst (exts σ) t ]
subst σ (s ↦ t) = subst σ s ↦ subst σ t
subst σ (#_ a ⦃ l ⦄) = σ l
subst σ nat = nat

infix 5 subst₁
subst₁ : ∀ {Δ} → (a : String) → Type (a ∷ Δ) → Type [] → Type Δ
subst₁ a t s = subst σ t
  where σ : ∀ {Δ a b} → a ∈ b ∷ Δ → Type Δ
        σ         (here P.refl) = embed []⊆Δ s
        σ {a = a} (there x)   = #_ a ⦃ x ⦄

syntax subst₁ a t s = t [ a / s ]

lookupT : ∀ {Δ a} → a ∈ Δ → TEnv Δ → Type []
lookupT (here _)  (x ∷ _)  = x
lookupT (there x) (_ ∷ nv) = lookupT x nv
 
{-# TERMINATING #-}
Val : ∀ {Δ} → Type Δ → TEnv Δ → Set 
Val ∀[ a ⇒ t ]   δ = (s : Type []) → Val t (s ∷ δ)
Val (s ↦ t)      δ = Val s δ → Val t δ
Val (#_ a ⦃ l ⦄) δ = Val (lookupT l δ) []
Val nat          δ = ℕ

data Term (Δ : TyCtx) (Γ : Ctx Δ) : Type Δ → Set where

  ƛ_⇒_ : ∀ {s t}
         → (x : String) → Term Δ ((x , s) ∷ Γ) t
         → Term Δ Γ (s ↦ t)
         
  _·_  : ∀ {s t}
         → Term Δ Γ (s ↦ t) → Term Δ Γ s
         → Term Δ Γ t
         
  `_   : ∀ {t}
         → (x : String) → ⦃ (x , t) ∈ Γ ⦄
         → Term Δ Γ t
         
  Λ_⇒_ :   (a : String)
         → {t : Type (a ∷ Δ)} → Term (a ∷ Δ) ⟪ Γ ⟫ t
         → Term Δ Γ ∀[ a ⇒ t ]
  
  _·#_ : ∀ {a t}
         → Term Δ Γ ∀[ a ⇒ t ] → (s : Type [])
         → Term Δ Γ (t [ a / s ])
  
  nlit : ℕ → Term Δ Γ nat
  
  add  :   Term Δ Γ nat → Term Δ Γ nat
         → Term Δ Γ nat


id : Term [] [] ∀[ "a" ⇒ (# "a") ↦ (# "a") ]
id = Λ "a" ⇒ (ƛ "x" ⇒ (` "x"))

idid : Term [] [] ∀[ "a" ⇒ (# "a") ↦ (# "a") ]
idid = (id ·# _) · id

id10 : Term [] [] nat
id10 = (id ·# _) · nlit 10

Env : ∀ {Δ} → (Γ : Ctx Δ) → (δ : TEnv Δ) → Set
Env Γ δ = All (λ (_ , t) → Val t δ) Γ

lookupV : ∀ {Δ} {Γ : Ctx Δ} {x t} {δ : TEnv Δ} → (x , t) ∈ Γ → Env Γ δ → Val t δ
lookupV (here P.refl) (v ∷ _)  = v
lookupV (there x)   (_ ∷ nv) = lookupV x nv

lookupT-ext : ∀ {Δ : TyCtx} {a : String} {l : a ∈ Δ} {δ : TEnv Δ} {s : Type []}
              → lookupT l δ P.≡ lookupT (extend (a ∷ʳ ⊆-refl) l) (s ∷ δ) 
lookupT-ext {x ∷ Δ} {l = here P.refl} {δ = δ}
 = P.refl
lookupT-ext {x ∷ Δ} {l = there l} {δ = t ∷ δ} {s}
 rewrite lookupT-ext {Δ = Δ} {l = l} {δ = δ} {t} = P.refl

convert : ∀ {Δ δ s a} → (t : Type (a ∷ Δ)) → Val t (s ∷ δ) P.≡ Val (t [ a / s ]) δ
convert ∀[ b ⇒ t ] = {!!}
convert (s ↦ t) = P.cong₂ (λ A B → A → B) (convert s) (convert t)
convert (# a) = {!!}
convert nat = P.refl

extv : ∀ {Δ a} {t : Type Δ} {s : Type []} {δ : TEnv Δ} → Val t δ P.≡ Val (embed (a ∷ʳ ⊆-refl) t) (s ∷ δ) 
extv {t = ∀[ b ⇒ t ]} {s} {δ} = {!!}
extv {t = t ↦ u} {s} {δ} = P.cong₂ (λ A B → A → B) (extv {t = t}) (extv {t = u})
extv {t = #_ a ⦃ l ⦄} {s} {δ} = P.cong (λ t → Val {Δ = []} t []) {x = lookupT l δ} {y = lookupT (extend (a ∷ʳ ⊆-refl) l) (s ∷ δ)} (lookupT-ext {l = l} {δ = δ} {s = s})
extv {t = nat} {s} {δ} = P.refl

ext-env : ∀ {Δ} {a : String} {s : Type []} {Γ : Ctx Δ} {δ : TEnv Δ} → Env Γ δ → Env (⟪_⟫ {a = a} Γ) (s ∷ δ)
ext-env [] = []
ext-env {Δ} {a} {s} {δ = δ} (_∷_ {x} v nv) rewrite extv {_} {a} {proj₂ x} {s} {δ} = v ∷ ext-env nv

⟦_⟧ : ∀ {Δ Γ t} → Term Δ Γ t → (δ : TEnv Δ) → (γ : Env Γ δ) → Val t δ 
⟦ ƛ x ⇒ e          ⟧ δ γ = λ v → ⟦ e ⟧ δ (v ∷ γ)
⟦ e₁ · e₂          ⟧ δ γ = ⟦ e₁ ⟧ δ γ (⟦ e₂ ⟧ δ γ)
⟦ `_ _ ⦃ x ⦄       ⟧ δ γ = lookupV x γ
⟦ Λ a ⇒ e          ⟧ δ γ = λ s → ⟦ e ⟧ (s ∷ δ) (ext-env γ)
⟦ _·#_ {t = t} e s ⟧ δ γ rewrite P.sym (convert {δ = δ} {s = s} t) = ⟦ e ⟧ δ γ s
⟦ nlit n           ⟧ δ γ = n
⟦ add e₁ e₂        ⟧ δ γ = ⟦ e₁ ⟧ δ γ + ⟦ e₂ ⟧ δ γ

-- Evaluate programs, i.e. closed terms
⟦_⟧prog : ∀ {t} → Term [] [] t → Val t []
⟦ e ⟧prog = ⟦ e ⟧ [] []

