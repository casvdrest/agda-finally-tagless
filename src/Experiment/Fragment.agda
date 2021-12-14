{-# OPTIONS --overlapping-instances #-}
module Experiment.Fragment where 

open import Experiment.ListSyntax

import Data.Bool    as B 
import Data.Nat     as N 
open import Data.Product renaming (_×_ to _P×_ )
import Data.Sum     as S 
import Data.List    as L
open import Data.Unit using (⊤ ; tt)
open import Data.String
open import Data.Empty

import Relation.Binary.PropositionalEquality as P
open import Relation.Unary using (IUniversal ; _⇒_)

open import Function
open import Level renaming (suc to sucL)

open import Experiment.Desc

module _ where 

  variable a b c : Set 

  {- Various types -} 

  NatT : Constructor
  NatT = "nat" , `1

  nat : ∀ {T} → ⦃ _ : NatT ≼ T ⦄ → Mu T
  nat = inject (lift tt) 

  BoolT : Constructor
  BoolT = "bool" , `1

  bool : ∀ {T} → ⦃ BoolT ≼ T ⦄ → Mu T
  bool = inject (lift tt)

  FunT : Constructor
  FunT = "fun" , `var `× `var

  _↦_ : ∀ {T} → ⦃ FunT ≼ T ⦄ → Mu T → Mu T → Mu T
  s ↦ t = inject (s , t)

  ProdT : Constructor
  ProdT = "product" , `var `× `var

  _×_ : ∀ {T} → ⦃ ProdT ≼ T ⦄ → Mu T → Mu T → Mu T
  s × t = inject (s , t)

  SumT : Constructor
  SumT = "sum" , `var `× `var

  _⊎_ : ∀ {T} → ⦃ SumT ≼ T ⦄ → Mu T → Mu T → Mu T
  s ⊎ t = inject (s , t)
  
  {- Contexts & instance search for typed De Bruijn -} 

  Ctx : Set → Set
  Ctx T = L.List (String P× T)
  
  data _∶_∈_ {T} (x : String) (t : T) : Ctx T → Set where
    here  : ∀ {Γ} → x ∶ t ∈ ((x , t) L.∷ Γ)
    there : ∀ {Γ y s} → x ∶ t ∈ Γ → x ∶ t ∈ ((y , s) L.∷ Γ) 

  instance ∈-here : ∀ {T} {Γ x} {t : T} → x ∶ t ∈ ((x , t) L.∷ Γ)
  ∈-here = here

  instance ∈-there : ∀ {T} {Γ x y s} {t : T} → ⦃ _ : x ∶ t ∈ Γ ⦄ → x ∶ t ∈ ((y , s) L.∷ Γ)
  ∈-there ⦃ w ⦄ = there w

  Repr : TypeDesc → Set₁
  Repr T = Ctx (Mu T) → Mu T → Set


  {- Language Fragments -}

  constrain : TypeDesc →  L.List Constructor → Set₁ → Set₁
  constrain T L.[] A = A
  constrain T (C L.∷ types) A = ⦃ C ≼ T ⦄ → constrain T types A

  record Fragment (types : L.List Constructor) : Set₁ where
    field sem : {T : TypeDesc} → constrain T types (Repr T → Set)  

  open Fragment


  {- λ-abstraction, application, and variables -} 

  record Lambda {T} ⦃ _ : FunT ≼ T ⦄ (ρ : Repr T) : Set where
    infixl 9 _·_
    infix  2 ƛ_⇒_
    infix  10 `_
    field
      ƛ_⇒_ : ∀ {Γ s t} → (x : String) → ρ ((x , s) L.∷ Γ) t → ρ Γ (s ↦ t) 
      _·_  : ∀ {Γ s t} → ρ Γ (s ↦ t) → ρ Γ s → ρ Γ t
      `_   : ∀ {Γ t}   → (x : String) → ⦃ x ∶ t ∈ Γ ⦄ → ρ Γ t

  LambdaF : Fragment [ FunT ]
  LambdaF .sem = Lambda

  {- Let-binding -} 

  record Let {T} ⦃ _ : FunT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 lett_∷=_inn_
    field
      lett_∷=_inn_ : ∀ {Γ s t} → (x : String) → ρ Γ s → ρ ((x , s) L.∷ Γ) t → ρ Γ t 

  LetF : Fragment [ FunT ]
  LetF .sem = Let


  {- Boolean expressions -} 

  record Boolean {T} ⦃ _ : BoolT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 ¬_
    infix 4 _∧_
    infix 3 _∨_
    field
      blit : ∀ {Γ} → B.Bool → ρ Γ bool
      ¬_   : ∀ {Γ} → ρ Γ bool → ρ Γ bool
      _∧_  : ∀ {Γ} → ρ Γ bool → ρ Γ bool → ρ Γ bool 
      _∨_  : ∀ {Γ} → ρ Γ bool → ρ Γ bool → ρ Γ bool

  BoolF : Fragment [ BoolT ]
  BoolF .sem = Boolean
  

  {- Natural number expressions -} 

  record Nats {T} ⦃ _ : NatT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 4 _*_
    infix 3 _+_
    field
      nlit : ∀ {Γ} → N.ℕ → ρ Γ nat  
      _+_  : ∀ {Γ} → ρ Γ nat → ρ Γ nat → ρ Γ nat
      _*_  : ∀ {Γ} → ρ Γ nat → ρ Γ nat → ρ Γ nat

  NatsF : Fragment [ NatT ]
  NatsF .sem = Nats
  

  {- NatCase  -} 
  
  record NatElim {T} ⦃ _ : NatT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 ncase_of⟨Z⇒_⟩⟨S_⇒_⟩
    field
      ncase_of⟨Z⇒_⟩⟨S_⇒_⟩ : ∀ {Γ t} → ρ Γ nat → ρ Γ t → (x : String) → ρ ((x , nat) L.∷ Γ) t → ρ Γ t 

  NCaseF : Fragment [ NatT ]
  NCaseF .sem = NatElim


  {- LEQ for natural numbers -} 

  record Ord {T} ⦃ _ : NatT ≼ T ⦄ ⦃ _ : BoolT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 2 _≤_
    field
      _≤_ : ∀ {Γ} → ρ Γ nat → ρ Γ nat → ρ Γ bool 

  OrdF : Fragment [ NatT , BoolT ]
  OrdF .sem = Ord


  {- Conditionals -} 

  record Cond {T} ⦃ _ : BoolT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 if_then_else_
    field
      if_then_else_ : ∀ {Γ t} → ρ Γ bool → ρ Γ t → ρ Γ t → ρ Γ t

  CondF : Fragment [ BoolT ]
  CondF .sem = Cond


  {- Product types -}

  record Product {T} ⦃ _ : ProdT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 2 _,,_
    field
      _,,_ : ∀ {Γ s t} → ρ Γ s → ρ Γ t → ρ Γ (s × t)
      fst : ∀ {Γ s t} → ρ Γ (s × t) → ρ Γ s
      snd : ∀ {Γ s t} → ρ Γ (s × t) → ρ Γ t

  ProductF : Fragment [ ProdT ]
  ProductF .sem = Product


  {- Sum Types -} 

  record Sum {T} ⦃ _ : SumT ≼ T ⦄ (ρ : Repr T) : Set where
    field
      inl   : ∀ {Γ s t} → ρ Γ s → ρ Γ (s ⊎ t)
      inr   : ∀ {Γ s t} → ρ Γ t → ρ Γ (s ⊎ t)

  SumF : Fragment [ SumT ]
  SumF .sem = Sum
  

  {- Sum elimination (either) -} 

  record SumElim {T} ⦃ _ : SumT ≼ T ⦄ ⦃ _ : FunT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 ⟪_,_⟫
    field
      ⟪_,_⟫ : ∀ {Γ s t u} → ρ Γ (s ↦ u) → ρ Γ (t ↦ u) → ρ Γ ((s ⊎ t) ↦ u)

  SumElimF : Fragment [ SumT , FunT ]
  SumElimF .sem = SumElim
  

  {- Recursive functions -} 

  record Fix {T} ⦃ _ : FunT ≼ T ⦄ (ρ : Repr T) : Set where
    field
      μ_,_⇒_ : ∀ {Γ s t} → (f x : String) → ρ ((x , s) L.∷ (f , (s ↦ t)) L.∷ Γ) t → ρ Γ (s ↦ t)

  FixF : Fragment [ FunT ]
  FixF .sem = Fix

  open Lambda  ⦃...⦄ public
  open Let     ⦃...⦄ public
  open Boolean ⦃...⦄ public 
  open Nats    ⦃...⦄ public 
  open NatElim ⦃...⦄ public 
  open Ord     ⦃...⦄ public 
  open Cond    ⦃...⦄ public 
  open Product ⦃...⦄ public 
  open Sum     ⦃...⦄ public 
  open SumElim ⦃...⦄ public 
  open Fix     ⦃...⦄ public 


  {- Language composition -}

  -- When composing two languaegs, it may be that they impose different
  -- constraints on the set of types.  We use witnesses of a proof-relevant
  -- ternary relation on lists (supplied by the user) to mediate the constraints
  -- of different languages.

  -- First, bring in some dependencies from ternary.agda and stdlib

  open import Relation.Ternary.Core 
  open Rel₃ ⦃...⦄ hiding (_≤_)

  open import Data.These 
  
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Properties
  open import Data.List.Relation.Unary.Any hiding (lookup)
  open import Data.List.Relation.Unary.All 

  infixr 9 _⋈_
  _⋈_ : ∀ {a ℓ} {A : Set a} → (P Q : A → Set ℓ) → A → Set ℓ
  (P ⋈ Q) x = These (P x) (Q x)

  -- List unions, as a ternary relation
  --
  -- Read as: zs is a union of xs and ys, iff:
  -- - every element of xs is in zs
  -- - every element of ys is in zs
  -- - every element of zs is either in xs, in ys, or in both.
  -- 
  record ListUnion {ℓ} {A : Set ℓ} (xs ys zs : L.List A) : Set ℓ where
    field
      inj-xs  : ∀[ Member xs ⇒ Member zs ]
      inj-ys  : ∀[ Member ys ⇒ Member zs ]

      from-zs : ∀[ Member zs ⇒ Member xs ⋈ Member ys ]

      -- TODO: inverse laws? e.g. from-zs ∘ inj-xs ≈ id

  open ListUnion

  instance list-rel : ∀ {ℓ} {A : Set ℓ} → Rel₃ (L.List A)
  Rel₃._∙_≣_ list-rel = ListUnion

  -- TODO: use defs from ternary.agda
  ∙-disjoint : ∀ {ℓ} {A : Set ℓ} {xs ys : L.List A} → xs ∙ ys ≣ (xs L.++ ys)
  inj-xs   ∙-disjoint            = ∈-++⁺ˡ
  inj-ys   ∙-disjoint            = ∈-++⁺ʳ _ 
  from-zs (∙-disjoint {xs = xs}) = S.[ this , that ] ∘ ∈-++⁻ xs

  ∙-copy : ∀ {ℓ} {A : Set ℓ} {xs : L.List A} → xs ∙ xs ≣ xs
  inj-xs  ∙-copy = id
  inj-ys  ∙-copy = id
  from-zs ∙-copy = λ x → these x x
  
  -- A language is just a bunch of constructs (fragments), that share a common
  -- set of constraints on their index type. 
  record Language (types : L.List Constructor) : Set₁ where
    constructor ⟪_⟫
    field constructs : L.List (Fragment types)

  open Language

  -- Strengthen the assumed type constraints of a fragment
  --
  -- Alternatively we could say that Fragment is a presheaf over the category
  -- induced by -⊆-
  fragment-mono : ∀ {xs ys} → ys ⊇ xs → Fragment xs → Fragment ys
  fragment-mono ys⊇xs f .sem = gather (discharge ys⊇xs (f .sem))

    where gather : ∀ {T A} {xs : L.List Constructor}
                   → (All (λ C → C ≼ T) xs → A)
                   → constrain T xs A 
          gather {xs = L.[]} f = f []
          gather {xs = x L.∷ xs} f ⦃ C ⦄ = gather {xs = xs} λ xs → f (C ∷ xs)

          discharge : ∀ {T A} {xs ys : L.List Constructor}
                      → ys ⊇ xs → constrain T xs A
                      → All (λ C → C ≼ T) ys → A
          discharge {xs = L.[]}     ys⊇xs ca cs = ca
          discharge {xs = C L.∷ xs} (x∈ys ∷ ys⊇xs) ca cs
            = discharge ys⊇xs (ca ⦃ lookup cs x∈ys ⦄) cs

  -- The same goes for Language
  language-mono : ∀ {xs ys} → ys ⊇ xs → Language xs → Language ys
  language-mono ys⊇xs l .constructs = L.map (fragment-mono ys⊇xs) (l .constructs)

  ⊆-fromMembership : ∀ {a} {A : Set a} {xs ys : L.List A}
                     → ∀[ Member xs ⇒ Member ys ] → xs ⊆ ys 
  ⊆-fromMembership {xs = L.[]}     f
    = []
  ⊆-fromMembership {xs = x L.∷ xs} f
    = f (here P.refl) ∷ ⊆-fromMembership {xs = xs} λ x → f (there x)

  union→⊇₁ : ∀ {a} {A : Set a} {xs ys zs : L.List A} → xs ∙ ys ≣ zs → zs ⊇ xs
  union→⊇₁ σ = ⊆-fromMembership (σ .inj-xs)

  union→⊇₂ : ∀ {a} {A : Set a} {xs ys zs : L.List A} → xs ∙ ys ≣ zs → zs ⊇ ys
  union→⊇₂ σ = ⊆-fromMembership (σ .inj-ys)

  -- Compose two languages with the same type constraints
  _⊕_ : ∀[ Language ⇒ Language ⇒ Language ]
  (l₁ ⊕ l₂) .constructs = l₁ .constructs L.++ l₂ .constructs

  -- Compose two languages with heterogeneous type constraints, using a
  -- user-supplied witness σ to mediate between the constraints of l₁ and l₂
  ⊕[_] : ∀[ Language ✴ Language ⇒ Language ]
  ⊕[ l₁ ∙⟨ σ ⟩ l₂ ] = language-mono (union→⊇₁ σ) l₁ ⊕ language-mono (union→⊇₂ σ) l₂

  -- Convenient syntax for composing anonymous languages
  infixr 1 _⊕⟨_⟩_
  _⊕⟨_⟩_ : ∀ {xs ys zs} → L.List (Fragment xs) → xs ∙ ys ≣ zs → L.List (Fragment ys) → L.List (Fragment zs)
  fs₁ ⊕⟨ σ ⟩ fs₂ = ⊕[ (λ where .constructs → fs₁) ∙⟨ σ ⟩ (λ where .constructs → fs₂) ] .constructs

  -- {- Calculate the type of terms in a language -} 

  -- Abstract over a set of type constraints 
  abstr : L.List (Set → Set) → (T : Set) → Set
  abstr L.[] T = T
  abstr (C L.∷ ts) T = C T → abstr ts T

  -- Calculate a term type for a list of semantics (sems) constrained by a list
  -- of type constraints (types)
  --
  -- We proceed by induction over the list of type constraints (types), where at
  -- every step we apply the constraint at the head of the list to every bit of
  -- semantics.
  --
  -- At the end, when there are no more type constraints left (and thus all bits
  -- of semantics are unconstrained), we return the term type, S, with instance
  -- arguments for all the elements of sems.
  TermOf : ∀ {T}
           → (types : L.List Constructor)
           → (sems : L.List (constrain T types ((ρ : Repr T) → Set)))
           → Repr T
           → (Mu T → Set)
           → Set
  TermOf {T} L.[]       fs ρ S
    = L.foldr (λ C a → ⦃ C ρ ⦄ → a) (∃ λ t → S t) fs
  TermOf {T} (C L.∷ types) fs ρ S
    = ⦃ tyC : C ≼ T ⦄ → TermOf types (L.map (λ f → f ⦃ tyC ⦄) fs) ρ S 

  mkpair : ∀ {a b} {A : Set a} {B : A → Set b} → (x : A) → (y : B x) → Σ A B
  mkpair = _,_

  infix 0 mkpair
  syntax mkpair x y = y ⦂ x  

  -- Calcuate the type of terms in a language, using TermOf
  Term : ∀ {types}
         → Language types
         → Set₁
  Term {types = types} lang 
    = ∀ {T ρ} → TermOf {T} types (L.map (λ f → f .sem) (lang .constructs)) ρ (ρ L.[])


  {- Example languages -} 

  LBool : Language [ BoolT ]
  LBool .constructs = [ BoolF , CondF ]

  LArith : Language [ NatT ]
  LArith .constructs = [ NatsF ]

  LExpr = ⊕[ LBool ∙⟨ ∙-disjoint ⟩ LArith ] 

  miniML = ⟪ [ BoolF ]                 ⊕⟨ ∙-disjoint ⟩
             [ NatsF , NCaseF ]        ⊕⟨ ∙-disjoint ⟩
             [ LambdaF , FixF , LetF ]
           ⟫ 

  {- Some Terms -} 

  term₁ : Term LBool
  term₁ = (blit B.true ∧ blit B.false)
        ⦂ bool

  term₂ : Term LArith
  term₂ = ((nlit 1 + nlit 2) * nlit 3)
        ⦂ nat 

  term₃ : Term LExpr
  term₃ = 
    if
      blit B.true ∨ blit B.false
    then
      nlit 2 * nlit 2
    else
      nlit 3 + nlit 3
    ⦂ nat

  term₄ : Term ⟪ [ LambdaF ] ⊕⟨ ∙-disjoint ⟩ [ BoolF ] ⟫
  term₄ =
    (ƛ "x" ⇒ ` "x") · blit B.false
    ⦂ bool

  term₅ : Term
        ⟪ [ LambdaF  ] ⊕⟨ ∙-disjoint ⟩
          [ OrdF     ] ⊕⟨ ∙-copy     ⟩
          [ NatsF    ] ⊕⟨ ∙-disjoint ⟩
          [ BoolF    ]
        ⟫
  term₅ = ¬ nlit 10 ≤ ((ƛ "n" ⇒ ` "n" * ` "n") · nlit 3) ⦂ bool 

  term₆ : Term ⟪ [ LambdaF ] ⊕⟨ ∙-disjoint ⟩ [ OrdF ] ⊕⟨ ∙-copy ⟩ [ NatsF ] ⊕⟨ ∙-disjoint ⟩ [ CondF ] ⟫
  term₆ =
    if
      nlit 1 + nlit 2 ≤ nlit 3
    then
      (ƛ "x" ⇒ ` "x" + ` "x") · nlit 3
    else
      nlit 0
    ⦂ nat

  term₇ : Term miniML
  term₇ =
    lett
      "factorial" ∷=
        μ "rec" , "n" ⇒
         ncase ` "n"
           of⟨Z⇒
             nlit 1
           ⟩⟨S "m" ⇒
             ` "n" * (` "rec" · ` "m")
           ⟩
    inn
      ` "factorial" · nlit 6
    ⦂ nat



{- Calculate the type of an extensible and composable definitions of a semantics definition -} 

module _ where

  open Fragment 
  open import Data.List.Relation.Unary.All

  _~<_>~_ : ∀  {ℓ} 
              {types    : L.List Constructor}
            → (dom      : ∀[ ReprDesc (Set ℓ) ⇒ Repr ])
            → (bound    : All (ReprClause (Set ℓ)) types)
            → (fragment : Fragment types)
            → Set (sucL ℓ)
  _~<_>~_ {ℓ} {types = types} dom bound fragment = {T : TypeDesc} {V : ReprDesc (Set ℓ) T} → go T V types dom bound (fragment .sem)

    where go : ∀ {ℓ} 
               → (T        : TypeDesc)
               → (V        : ReprDesc (Set ℓ) T)
               → (types    : L.List Constructor)
               → (dom      : ∀[ ReprDesc (Set ℓ) ⇒ Repr ])
               → (bound    : All (ReprClause (Set ℓ)) types)
               → (fragment : constrain T types (Repr T → Set))
               → Set (sucL ℓ) 
          go     T V L.[]          dom []         fragment
            = Lift _ (fragment (dom V))
            
          -- We include a special case for singleton lists here, to avoid
          -- allways needing to wrap interpretations in a `Lift`.  Really,
          -- fragments should be level-polymorphic in the size of the image of
          -- the representation functor.
          go     T V (C L.∷ L.[] ) dom (rc ∷ [] ) fragment
            = ⦃ tx : C ≼ T ⦄ → ⦃ rc ◃ V ⦄ → fragment (dom V)
          go {ℓ} T V (C L.∷ types) dom (rc ∷ rcs) fragment
            = ⦃ tx : C ≼ T ⦄ → ⦃ rc ◃ V ⦄ → go T V types dom rcs (fragment ⦃ tx ⦄)

  -- A special case for constant representation functors 
  _~<>~_ : ∀  {types    : L.List Constructor}
            → (dom      : Set)
            → (fragment : Fragment types)
            → Set₁
  dom ~<>~ fragment = (λ _ _ _ → dom) ~< fill dom >~ fragment

    where fill : ∀ {types    : L.List Constructor}
                 → (dom      : Set)
                 → All (ReprClause Set) types 
          fill {types = L.[]}        dom = []
          fill {types = C L.∷ types} dom = (λ where .clause _ → dom) ∷ fill dom
