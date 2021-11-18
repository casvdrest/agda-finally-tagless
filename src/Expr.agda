module Expr where

open import Experiment.ListSyntax

import Data.Bool    as B 
import Data.Nat     as N 
open import Data.Product renaming (_×_ to _P×_ ; _,_ to _∙_)
import Data.Sum     as S 
import Data.List    as L

open import Relation.Unary using (IUniversal)

variable a b c T : Set 

record FunTy (T : Set) : Set where
  field
    _↦_ : T → T → T

open FunTy ⦃...⦄

record BoolTy (T : Set) : Set where
  field
    bool : T

open BoolTy ⦃...⦄


record NatTy (T : Set) : Set where
  field
    nat : T

open NatTy ⦃...⦄

record ProdTy (T : Set) : Set where
  field
    _×_ : T → T → T 

open ProdTy ⦃...⦄

record SumTy (T : Set) : Set where
  field
    _⊎_ : T → T → T 

open SumTy ⦃...⦄

record Lambda {T} ⦃ _ : FunTy T ⦄ (ρ : T → Set) : Set where
  field
    lam : ∀ {s t} → (ρ s → ρ t) → ρ (s ↦ t)
    app : ∀ {s t} → ρ (s ↦ t) → ρ s → ρ t

record Boolean {T} ⦃ _ : BoolTy T ⦄ (ρ : T → Set) : Set where
  field
    blit : B.Bool → ρ bool
    ¬_   : ρ bool → ρ bool
    _∧_  : ρ bool → ρ bool → ρ bool 
    _∨_  : ρ bool → ρ bool → ρ bool

record Nats {T} ⦃ _ : NatTy T ⦄ (ρ : T → Set) : Set where
  field
    nlit : N.ℕ → ρ nat  
    _+_  : ρ nat → ρ nat → ρ nat
    _*_  : ρ nat → ρ nat → ρ nat

record Ord {T} ⦃ _ : NatTy T ⦄ ⦃ _ : BoolTy T ⦄ (ρ : T → Set) : Set where
  field
    _≤_ : ρ nat → ρ nat → ρ bool

record Cond {T} ⦃ _ : BoolTy T ⦄ (ρ : T → Set) : Set where
  field
    if_then_else_ : ∀ {t} → ρ bool → ρ t → ρ t → ρ t

record Product {T} ⦃ _ : ProdTy T ⦄ (ρ : T → Set) : Set where
  field
    _,_ : ∀ {s t} → ρ s → ρ t → ρ (s × t)
    fst : ∀ {s t} → ρ (s × t) → ρ s
    snd : ∀ {s t} → ρ (s × t) → ρ t

record Sum {T} ⦃ _ : SumTy T ⦄ (ρ : T → Set) : Set where
  field
    inl   : ∀ {s t} → ρ s → ρ (s ⊎ t)
    inr   : ∀ {s t} → ρ t → ρ (s ⊎ t)

record SumElim {T} ⦃ _ : SumTy T ⦄ ⦃ _ : FunTy T ⦄ (ρ : T → Set) : Set where 
  field
    [_,_] : ∀ {s t u} → ρ (s ↦ u) → ρ (t ↦ u) → ρ ((s ⊎ t) ↦ u)

record Fix {T} ⦃ _ : FunTy T ⦄ (ρ : T → Set) : Set where
  field
    fix : ∀ {s t} → ρ ((s ↦ t) ↦ (s ↦ t)) → ρ (s ↦ t) 

open Lambda  ⦃...⦄
open Boolean ⦃...⦄
open Nats    ⦃...⦄
open Ord     ⦃...⦄
open Cond    ⦃...⦄
open Product ⦃...⦄
open Sum     ⦃...⦄
open SumElim ⦃...⦄
open Fix     ⦃...⦄

Term : {T : Set} → (cs : L.List ((T → Set) → Set)) → T → (T → Set) → Set
Term cs t ρ = L.foldr (λ C a → ⦃ _ : C ρ ⦄ → a) (ρ t) cs

{- Some terms -}

term₁ : ⦃ _ : FunTy T ⦄ ⦃ _ : BoolTy T ⦄
      → ∀[ Term [ Lambda ∙ Boolean ] bool ] 
term₁ = app (lam (λ x → x)) (blit B.false)

term₂ : ⦃ _ : BoolTy T ⦄ ⦃ _ : NatTy T ⦄ ⦃ _ : FunTy T ⦄
      → ∀[ Term [ Boolean ∙ Ord ∙ Nats ∙ Lambda ] bool ]
term₂ = ¬ (nlit 10 ≤ app (lam λ x → x * x) (nlit 3))

term₃ : ⦃ _ : FunTy T ⦄ ⦃ _ : BoolTy T ⦄ ⦃ _ : NatTy T ⦄
      → ∀[ Term [ Lambda ∙ Ord ∙ Cond ∙ Nats ] nat ]
term₃ =
 if
   (nlit 1 + nlit 2) ≤ nlit 3
 then
   app (lam (λ x → x * x)) (nlit 3)
 else
   nlit 0 

{- Interpreter -}

data Type : Set where
  `nat `bool : Type
  _`↦_ _`×_ _`⊎_ : Type → Type → Type 

Val : Type → Set
Val `nat = N.ℕ
Val `bool = B.Bool
Val (s `↦ t) = Val s → Val t
Val (s `× t) = Val s P× Val t
Val (s `⊎ t) = Val s S.⊎ Val t

instance type-fun : FunTy Type
type-fun ._↦_ = _`↦_

instance type-nat : NatTy Type
type-nat .nat = `nat

instance type-bool : BoolTy Type
type-bool .bool = `bool

instance type-product : ProdTy Type
type-product ._×_ = _`×_

instance type-sum : SumTy Type
type-sum ._⊎_ = _`⊎_

instance eval-lambda : Lambda Val
eval-lambda .lam = λ f x → f x
eval-lambda .app = λ f x → f x

instance eval-boolean : Boolean Val
eval-boolean .blit = λ x → x
eval-boolean .¬_   = B.not
eval-boolean ._∧_  = B._∧_
eval-boolean ._∨_  = B._∨_

instance eval-nats : Nats Val
eval-nats .nlit = λ x → x
eval-nats ._+_  = N._+_
eval-nats ._*_  = N._*_

instance eval-ord : Ord Val
eval-ord ._≤_ = λ n m → B.not (m N.<ᵇ n)

instance eval-cond : Cond Val
eval-cond .if_then_else_ = B.if_then_else_

instance eval-prod : Product Val
eval-prod ._,_ = _∙_
eval-prod .fst = proj₁
eval-prod .snd = proj₂

instance eval-sum : Sum Val
eval-sum .inl = S.inj₁
eval-sum .inr = S.inj₂

instance eval-sum-elim : SumElim Val
eval-sum-elim .[_,_] = S.[_,_]

{-# TERMINATING #-} -- nope
fix' : ∀ {A B : Set} → ((A → B) → A → B) → A → B
fix' f = f (fix' f)

instance eval-fix : Fix Val
eval-fix .fix = fix' 

term₁-eval : B.Bool
term₁-eval = term₁

term₂-eval : B.Bool
term₂-eval = term₂

term₃-eval : N.ℕ
term₃-eval = term₃


{- Pretty printing -}

open import Data.String
open import Agda.Builtin.String renaming (primShowNat to showℕ)

PP : T → Set
PP _ = N.ℕ -> String

showB : B.Bool → String
showB B.true  = "true"
showB B.false = "false"

instance pp-lambda : Lambda PP
pp-lambda .lam = λ f n → let x = "x" ++ showℕ n in "(λ" ++ x ++ " → " ++ f (λ _ → x) (N.suc n) ++ ")"  
pp-lambda .app = λ f x n → f n ++ " " ++ x n

instance pp-boolean : Boolean PP
pp-boolean .blit = λ x _ → showB x
pp-boolean .¬_   = λ x n → "¬ " ++ x n
pp-boolean ._∧_  = λ x y n → x n ++ " ∧ " ++ y n
pp-boolean ._∨_  = λ x y n → x n ++ " ∨ " ++ y n


instance pp-nats : Nats PP
pp-nats .nlit = λ n _ → showℕ n
pp-nats ._+_ = λ x y n → x n ++ " + " ++ y n
pp-nats ._*_ = λ x y n → x n ++ " * " ++ y n

instance pp-ord : Ord PP
pp-ord ._≤_ = λ x y n → x n ++ " ≤ " ++ y n

instance pp-cond : Cond PP
pp-cond .if_then_else_ = λ c t e n → "if " ++ c n ++ " then " ++ t n ++ " else " ++ e n 

instance pp-prod : Product PP
pp-prod ._,_ = λ x y n → x n ++ " , " ++ y n 
pp-prod .fst = λ x n → "fst " ++ x n 
pp-prod .snd = λ y n → "snd " ++ y n

instance pp-sum : Sum PP
pp-sum .inl = λ x n → "inl " ++ x n 
pp-sum .inr = λ x n → "inr " ++ x n

instance pp-sum-elim : SumElim PP
pp-sum-elim .[_,_] = λ l r n → "[ " ++ l n ++ " , " ++ r n ++ "]" 

instance pp-fix : Fix PP
pp-fix .fix = λ x n → "fix " ++ x n

variable s t u : T

term₁-pp : String
term₁-pp = term₁ 0

term₂-pp : String
term₂-pp = term₂ 0

term₃-pp : String
term₃-pp = term₃ 0
