module Experiment.Semantics where

open import Experiment.Desc
open import Experiment.Fragment

open import Function
open import Level 

import Data.Bool as B
import Data.Nat  as N
import Data.Sum  as S 
open import Data.Unit using (⊤ ; tt)
import Data.List as L
open import Data.String

open import Data.Product renaming (_×_ to _P×_)

open import Relation.Unary
open import Data.List.Relation.Unary.All

{- Interpretation Semantics -}
module Interpretation where 

   -- Environments. Only work for representation functors that target `Set`
  data Env {T} (V : ReprDesc Set T) : Ctx (Mu T) → Set where
  
    []  : Env V L.[] 

    _∷_ : ∀ {Γ} {x : String} {t : Mu T}
          → < V > t → Env V Γ
          → Env V ((x , t) L.∷ Γ) 

  fetch : ∀  {T} {V : ReprDesc Set T} x {t Γ} → ⦃ x ∶ t ∈ Γ ⦄ → Env V Γ → < V > t
  fetch _ ⦃ here ⦄      (v ∷ _)  = v
  fetch _ ⦃ (there l) ⦄ (_ ∷ nv) = fetch _ ⦃ l ⦄ nv

  -- Interpretation ≈ a function from environment to value
  Interp : ∀[ ReprDesc Set ⇒ Repr ]
  Interp V Γ t = Env V Γ → < V > t


  --
  -- Functions

  FunV : ReprClause Set FunT
  FunV .clause (s , t) = s → t

  eval-lambda : Interp ~< FunV ∷ [] >~ LambdaF
  Lambda.ƛ_⇒_ eval-lambda = λ _ f nv → ↑ λ x → f (x ∷ nv)
  Lambda._·_  eval-lambda = λ f x nv → ↓ (f nv) $ x nv
  Lambda.`    eval-lambda = λ x nv → fetch x nv

  eval-let : Interp ~< FunV ∷ [] >~ LetF 
  eval-let .lett_∷=_inn_ = λ x e₁ e₂ nv → e₂ (e₁ nv ∷ nv)

  {-# TERMINATING #-} -- nope
  fix' : ∀ {A B : Set} → ((A → B) → A → B) → A → B
  fix' f = f (fix' f)
  
  eval-fix : Interp ~< FunV ∷ [] >~ FixF 
  eval-fix .μ_,_⇒_ = λ _ x e nv → ↑ (fix' λ f v → e (v ∷ (↑ f) ∷ nv))


  -- 
  -- Booleans
 
  BoolV : ReprClause Set BoolT
  BoolV .clause (lift tt) = B.Bool

  eval-boolean : Interp ~< BoolV ∷ [] >~ BoolF
  eval-boolean .blit = λ x   _  → ↑ x  
  eval-boolean .¬_   = λ x   nv → ↑ (B.not (↓ (x nv)))
  eval-boolean ._∧_  = λ x y nv → ↑ ((↓ (x nv)) B.∧ (↓ (y nv))) 
  eval-boolean ._∨_  = λ x y nv → ↑ ((↓ (x nv)) B.∨ (↓ (y nv))) 

  eval-cond : Interp ~< BoolV ∷ [] >~ CondF 
  eval-cond .if_then_else_
    = λ c t e nv → B.if ↓ (c nv) then (t nv) else (e nv)


  --
  -- Natural numbers 

  NatV : ReprClause Set NatT
  NatV .clause (lift tt) = N.ℕ

  eval-nats : Interp ~< NatV ∷ [] >~ NatsF 
  eval-nats .nlit = λ x _ → ↑ x  
  eval-nats ._+_  = λ x y nv → ↑ ((↓ (x nv)) N.+ (↓ (y nv))) 
  eval-nats ._*_  = λ x y nv → ↑ ((↓ (x nv)) N.* (↓ (y nv))) 

  eval-ncase : Interp ~< NatV ∷ [] >~ NCaseF
  eval-ncase .ncase_of⟨Z⇒_⟩⟨S_⇒_⟩
    = λ n z _ s nv →
        Function.case ↓ (n nv) of
          λ { N.zero    → z nv
            ; (N.suc k) → s (↑ k ∷ nv)
            }

  eval-ord : Interp ~< NatV ∷ BoolV ∷ [] >~ OrdF
  eval-ord ._≤_ = λ n m nv → ↑ (B.not (↓ (m nv) N.<ᵇ ↓ (n nv)))


  --
  -- Products/pairs

  ProdV : ReprClause Set ProdT
  ProdV .clause (s , t) = s P× t
  
  eval-prod : Interp ~< ProdV ∷ [] >~ ProductF 
  eval-prod ._,,_ = λ x y nv → ↑ (x nv , y nv) 
  eval-prod .fst  = λ x nv → proj₁ (↓ (x nv)) 
  eval-prod .snd  = λ x nv → proj₂ (↓ (x nv)) 


  --
  -- Sums/either

  SumV : ReprClause Set SumT
  SumV .clause (s , t) = s S.⊎ t  

  eval-sum : Interp ~< SumV ∷ [] >~ SumF 
  eval-sum .inl = λ x nv → ↑ (S.inj₁ (x nv))
  eval-sum .inr = λ x nv → ↑ (S.inj₂ (x nv))
  
  eval-sum-elim : Interp ~< SumV ∷ FunV ∷ [] >~ SumElimF 
  eval-sum-elim .⟪_,_⟫ = λ x y nv → ↑ λ z → S.[ ↓ (x nv) , ↓ (y nv) ] (↓ z)


  -- test₁ : interp (BoolV ∷ []) {!term₁ .proj₂!} [] P.≡ B.false
  -- test₁ = P.refl

  -- test₂ : proj₂ term₂ [] P.≡ 9
  -- test₂ = P.refl

  -- test₃ : proj₂ term₃ [] P.≡ 4
  -- test₃ = P.refl

  -- test₄ : proj₂ term₄ [] P.≡ B.false
  -- test₄ = P.refl

  -- test₅ : proj₂ term₅ [] P.≡ B.true
  -- test₅ = P.refl

  -- test₆ : proj₂ term₆ [] P.≡ 6
  -- test₆ = P.refl

  -- test₇ : proj₂ term₇ [] P.≡ 720
  -- test₇ = P.refl


  {- Pretty printing -}
 
  open import Agda.Builtin.String renaming (primShowNat to showℕ)
  
  Pretty = String

  StringV : ReprClause Set C
  StringV .clause _ = String

  showB : B.Bool → String
  showB B.true  = "true"
  showB B.false = "false"
  
  pp-lambda : Pretty ~<>~ LambdaF 
  pp-lambda .ƛ_⇒_ = λ x f → "(λ" ++ x  ++ " → " ++ f ++ ")"  
  pp-lambda ._·_  = λ f x → f ++ " " ++ x
  pp-lambda .`_   = λ x → x

  pp-let : Pretty ~<>~ LetF 
  Let.lett_∷=_inn_ pp-let = λ x y z → "let " ++ x ++ " ∷= " ++ y ++ " in " ++ z
  
  pp-boolean : Pretty ~<>~ BoolF 
  pp-boolean .blit = λ x → showB x
  pp-boolean .¬_   = λ x → "¬ " ++ x
  pp-boolean ._∧_  = λ x y → x ++ " ∧ " ++ y
  pp-boolean ._∨_  = λ x y → x ++ " ∨ " ++ y
  
  pp-nats : Pretty ~<>~ NatsF 
  pp-nats .nlit = λ n → showℕ n
  pp-nats ._+_ = λ x y → x ++ " + " ++ y
  pp-nats ._*_ = λ x y → x ++ " * " ++ y

  pp-ncase : Pretty ~<>~ NCaseF 
  NatElim.ncase_of⟨Z⇒_⟩⟨S_⇒_⟩ pp-ncase
   = λ n z k s → "ncase " ++ n ++ " of ⟨Z⇒ " ++ z ++ " ⟩⟨S " ++ k ++ " ⇒ " ++ s ++ "⟩"

  pp-ord : Pretty ~<>~ OrdF  
  pp-ord ._≤_ = λ x y → x ++ " ≤ " ++ y
  
  pp-cond : Pretty ~<>~ CondF 
  pp-cond .if_then_else_ = λ c t e → "if " ++ c ++ " then " ++ t ++ " else " ++ e 
  
  pp-prod : Pretty ~<>~ ProductF 
  pp-prod ._,,_ = λ x y → x ++ " , " ++ y 
  pp-prod .fst = λ x → "fst " ++ x 
  pp-prod .snd = λ y → "snd " ++ y
  
  pp-sum : Pretty ~<>~ SumF  
  pp-sum .inl = λ x → "inl " ++ x 
  pp-sum .inr = λ x → "inr " ++ x
  
  pp-sum-elim : Pretty ~<>~ SumElimF 
  pp-sum-elim .⟪_,_⟫ = λ l r → "[ " ++ l ++ " , " ++ r ++ "]"

  pp-fix : Pretty ~<>~ FixF
  pp-fix .μ_,_⇒_  = λ rec x f → "μ " ++ rec ++ " " ++ x ++ " → " ++ f 
  
  -- test₈ : proj₂ term₁ P.≡ "true ∧ false"
  -- test₈ = P.refl

  -- -- test₉ : proj₂ term₂ P.≡ "1 + 2 * 3"
  -- -- test₉ = P.refl

  -- -- test₁₀ : proj₂ term₃ P.≡ "if true ∨ false then 2 * 2 else 3 + 3"
  -- -- test₁₀ = P.refl

  -- -- test₁₁ : proj₂ term₄ P.≡ "(λx → x) false"
  -- -- test₁₁ = P.refl

  -- -- test₁₂ : proj₂ term₅ P.≡ "¬ 10 ≤ (λn → n * n) 3"
  -- -- test₁₂ = P.refl

  -- -- test₁₃ : proj₂ term₆ P.≡ "if 1 + 2 ≤ 3 then (λx → x + x) 3 else 0"
  -- -- test₁₃ = P.refl

  -- -- test₁₄ : proj₂ term₇ P.≡ "let factorial ∷= μ rec n → ncase n of ⟨Z⇒ 1 ⟩⟨S m ⇒ n * rec m⟩ in factorial 6"
  -- -- test₁₄ = P.refl 
  
