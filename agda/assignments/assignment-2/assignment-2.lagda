\begin{code}

module assignment-2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total)
open import plfa.Relations using (_<_; z<s; s<s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Unary using (Decidable)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)
open plfa.Isomorphism.≃-Reasoning
open import plfa.Lists using (List; []; _∷_; [_]; [_,_]; [_,_,_]; [_,_,_,_];
  _++_; reverse; map; foldr; sum; All; Any; here; there; _∈_; ++-identityʳ;
  ++-assoc)

--------------------------------------------------------------------------------

id : {A : Set} → A → A
id x = x

--------------------------------------------------------------------------------

-- binaries

module Bin where

  data Bin : Set where
    nil : Bin
    x0_ : Bin → Bin
    x1_ : Bin → Bin

  inc : Bin → Bin
  inc nil = x1 nil
  inc (x0 b) = x1 b
  inc (x1 b) = x0 (inc b)

  to : ℕ → Bin
  to zero = x0 nil
  to (suc n) = inc (to n)

  from : Bin → ℕ
  from nil = 0
  from (x0 b) = from b + from b
  from (x1 b) = suc (from b + from b)

  from∘inc≡suc∘from : ∀ (x : Bin) → (from ∘ inc) x ≡ (suc ∘ from) x
  from∘inc≡suc∘from nil = refl
  from∘inc≡suc∘from (x0 x) = refl
  from∘inc≡suc∘from (x1 x)
    rewrite from∘inc≡suc∘from x | +-suc (from x) (from x) = refl

  from∘to≡id : ∀ (n : ℕ) → (from ∘ to) n ≡ n
  from∘to≡id zero = refl
  from∘to≡id (suc n) rewrite from∘inc≡suc∘from (to n) | from∘to≡id n = refl

  data One : Bin → Set
  data Can : Bin → Set

  data One where
    one : ∀ {b : Bin} → Can b → One (inc b)
  
  data Can where
    zero : Can (x0 nil)
    suc : ∀ {b : Bin} → One b → Can b

  -- increment preserves canonical bitstrings
  one-inc : ∀ {b : Bin} → One b → One (inc b)
  can-inc : ∀ {b : Bin} → Can b → Can (inc b)

  one-inc (one cb) = one (can-inc cb)
  can-inc zero = suc (one zero)
  can-inc (suc ob) = suc (one-inc ob)

  -- converting a natural to a bitstring always yields a canonical bitstring
  can∘to : ∀ {n : ℕ} → Can (to n)
  can∘to {zero} = zero 
  can∘to {suc n} = suc (one (can∘to {n}))

  -- converting a canonical bitstring to a natural and back is the identity

  -- auxiliary
  can-from∘inc≡suc∘from : ∀ {b : Bin} → Can b → from (inc b) ≡ suc (from b)
  can-from∘inc≡suc∘from {b} _ = from∘inc≡suc∘from b

  one-to∘from≡id : ∀ {b : Bin} → One b → to (from b) ≡ b
  can-to∘from≡id : ∀ {b : Bin} → Can b → to (from b) ≡ b

  one-to∘from≡id (one cb)
    rewrite can-from∘inc≡suc∘from cb  | can-to∘from≡id cb = refl
  can-to∘from≡id zero = refl
  can-to∘from≡id osb@(suc ob)
    rewrite can-from∘inc≡suc∘from osb | one-to∘from≡id ob = refl

--------------------------------------------------------------------------------
--
-- Equality
-- 
--------------------------------------------------------------------------------

-- exercise [≤-Reasoning] (stretch)

-- the proof of monotonicity from Chapter Relations can be written in a more
-- readable form by using an anologue of our notation for ≡-reasoning

-- define ≤-reasoning analogously, and use it to write out an alternative
-- proof that addition is monotonic with regard to inequality

-- rewrite both +-monoˡ-≤ and +-mono-≤

module ≤-Reasoning where

  infix  1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _≤-∎

  ≤-begin_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  ≤-begin x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  _ ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  _ ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z
      
  _≤-∎ : ∀ (x : ℕ) → x ≤ x
  zero ≤-∎ = z≤n
  suc x ≤-∎ = s≤s (x ≤-∎)

open ≤-Reasoning

+-monoʳ-≤ : ∀ {m p q : ℕ} → p ≤ q → m + p ≤ m + q
+-monoʳ-≤ {zero} p≤q = p≤q
+-monoʳ-≤ {suc m} {p} {q} p≤q = ≤-begin
  suc m + p    ≤⟨⟩
  suc (m + p)  ≤⟨ cong-suc (+-monoʳ-≤ p≤q) ⟩
  suc (m + q)  ≤⟨⟩
  suc m + q    ≤-∎
    where
      cong-suc : {x y : ℕ} → x ≤ y → suc x ≤ suc y
      cong-suc z≤n = s≤s z≤n
      cong-suc (s≤s x≤y) = s≤s (s≤s x≤y) 

+-monoˡ-≤ : ∀ {m n p : ℕ} → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ {m} {n} {p} m≤n = ≤-begin
  m + p  ≤⟨⟩
  m + p  ≤⟨ ≡-then-≤ (+-comm m p) ⟩
  p + m  ≤⟨ +-monoʳ-≤ m≤n ⟩
  p + n  ≤⟨ ≡-then-≤ (+-comm p n) ⟩
  n + p  ≤-∎
    where
      ≡-then-≤ : ∀ {m n : ℕ} → m ≡ n → m ≤ n
      ≡-then-≤ {zero} _ = z≤n
      ≡-then-≤ {suc _} refl = s≤s (≡-then-≤ refl)

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-begin
  m + p  ≤⟨ +-monoˡ-≤ m≤n ⟩
  n + p  ≤⟨ +-monoʳ-≤ p≤q ⟩
  n + q  ≤-∎

--------------------------------------------------------------------------------
--
-- Isomorphism
-- 
--------------------------------------------------------------------------------

-- exercise [≃-implies-≲]

-- show that every isomorphism implies an embedding

≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B = record
  { to      = _≃_.to A≃B
  ; from    = _≃_.from A≃B
  ; from∘to = _≃_.from∘to A≃B
  }

--------------------------------------------------------------------------------

-- exercise [_⇔_] (recommended)

-- equivalence of propositions (also known as “if and only if”):

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

-- show that equivalence is reflexive, symmetric, and transitive

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = record
  { to   = id
  ; from = id
  }

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B = record
  { to   = _⇔_.from A⇔B
  ; from = _⇔_.to A⇔B
  }

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C  → A ⇔ C
⇔-trans A⇔B B⇔C = record
  { to   = _⇔_.to B⇔C ∘ _⇔_.to A⇔B
  ; from = _⇔_.from A⇔B ∘ _⇔_.from B⇔C
  }

--------------------------------------------------------------------------------

-- exercise [Bin-embedding] (stretch)

-- establish that there is an embedding of ℕ into Bin

open Bin using (Bin)

ℕ-≲-Bin : ℕ ≲ Bin
ℕ-≲-Bin = record
  { to      = Bin.to
  ; from    = Bin.from
  ; from∘to = Bin.from∘to≡id 
  }

-- why is there not an isomorphism?

-- because of the leading-zero alternative representations for binaries

--------------------------------------------------------------------------------
--
-- Connectives
-- 
--------------------------------------------------------------------------------

-- exercise [⇔≃×] (recommended)

-- show that A ⇔ B is isomorphic to (A → B) × (B → A)

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
  { to      = λ A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩
  ; from    = λ{ ⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A }}
  ; from∘to = λ _ → refl
  ; to∘from = λ{ ⟨ _ , _ ⟩ → refl}
  }

--------------------------------------------------------------------------------

-- exercise [⊎-comm] (recommended)

-- show sum is commutative up to isomorphism

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to      = λ{ (inj₁ A) → inj₂ A ; (inj₂ B) → inj₁ B }
  ; from    = λ{ (inj₁ B) → inj₂ B ; (inj₂ A) → inj₁ A }
  ; from∘to = λ{ (inj₁ _) → refl   ; (inj₂ _) → refl   }
  ; to∘from = λ{ (inj₁ _) → refl   ; (inj₂ _) → refl   }
  }

--------------------------------------------------------------------------------

-- exercise [⊎-assoc]

-- show sum is associative up to isomorphism

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { to      = λ
    { (inj₁ (inj₁ A)) → inj₁ A
    ; (inj₁ (inj₂ B)) → inj₂ (inj₁ B)
    ; (inj₂ C)        → inj₂ (inj₂ C)
    }
  ; from    =  λ
    { (inj₁ A)        → inj₁ (inj₁ A)
    ; (inj₂ (inj₁ B)) → inj₁ (inj₂ B)
    ; (inj₂ (inj₂ C)) → inj₂ C
    }
  ; from∘to = λ
    { (inj₁ (inj₁ _)) → refl
    ; (inj₁ (inj₂ _)) → refl
    ; (inj₂ _)        → refl
    }
  ; to∘from = λ
    { (inj₁ _)        → refl
    ; (inj₂ (inj₁ _)) → refl
    ; (inj₂ (inj₂ _)) → refl
    }
  }

--------------------------------------------------------------------------------

-- exercise [⊥-identityˡ] (recommended)

-- show empty is the left identity of sums up to isomorphism

⊎-⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊎-⊥-identityˡ = record
  { to      = λ{ (inj₁ ()) ; (inj₂ A) → A }
  ; from    = λ A → inj₂ A
  ; from∘to = λ{ (inj₁ ()) ; (inj₂ A) → refl }
  ; to∘from = λ A → refl
  }

--------------------------------------------------------------------------------

-- exercise [⊥-identityʳ]

-- show empty is the right identity of sums up to isomorphism

⊎-⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊎-⊥-identityʳ {A} = ≃-begin
  (A ⊎ ⊥)  ≃⟨ ⊎-comm ⟩
  (⊥ ⊎ A)  ≃⟨ ⊎-⊥-identityˡ ⟩
  A        ≃-∎

--------------------------------------------------------------------------------

-- exercise [⊎-weak-×] (recommended)

-- show that the following property holds

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , _ ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

-- this is called a weak distributive law

-- give the corresponding distributive law, and explain how it relates
-- to the weak version

-- the correposing law is:
--   ×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)

-- for the stronger version, we can naturally infer (A × C), instead of only A
-- therefore, we have an isomorphism

--------------------------------------------------------------------------------

-- exercise [⊎×-implies-×⊎]

-- show that a disjunct of conjuncts implies a conjunct of disjuncts

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- does the converse hold?
-- if so, prove; if not, give a counterexample

-- ×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- does not hold

-- counterexample:
--   A = true
--   B = false
--   C = false
--   D = true
--   (A ⊎ C) × (B ⊎ D) is true
--   (A × B) ⊎ (C × D) is false

--------------------------------------------------------------------------------
--
-- Negation
-- 
--------------------------------------------------------------------------------

-- exercise [<-irreflexive] (recommended)

-- using negation, show that strict inequality is irreflexive, that is, n < n
-- holds for no n

<-irreflexive : ∀ {x : ℕ} → ¬ (x < x)
<-irreflexive (s<s x<x) = <-irreflexive x<x

--------------------------------------------------------------------------------

-- exercise [trichotomy]

-- skipped

--------------------------------------------------------------------------------

-- exercise [⊎-dual-×] (recommended)

-- show that conjunction, disjunction, and negation are
-- related by a version of De Morgan’s Law

postulate →-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

-- do we also have the following?
-- ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

{- 
  no, because we can't prove the [to], as in:
    ×-dual-⊎-to : ∀ {A B : Set} → ¬ (A × B) → (¬ A) ⊎ (¬ B)

  for the same reasons we can't prove ¬¬A → A

  but we can prove the [from] as follows:
-}

×-dual-⊎-from : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎-from (inj₁ ¬a) a×b = ¬a (proj₁ a×b)
×-dual-⊎-from (inj₂ ¬b) a×b = ¬b (proj₂ a×b)

--------------------------------------------------------------------------------

-- exercise [Classical] (stretch)

{-
  consider the following principles (for all A and B):

    Excluded Middle:             A ⊎ ¬ A
    Double Negation Elimination: ¬ ¬ A → A
    Peirce’s Law:                ((A → B) → A) → A
    Implication as disjunction:  (A → B) → ¬ A ⊎ B
    De Morgan:                   ¬ (¬ A × ¬ B) → A ⊎ B

  show that each of these implies all the others

-}

em→dne : ∀ {A B : Set} → (A ⊎ ¬ A) → (¬ ¬ A → A)
em→dne (inj₁ a) _ = a
em→dne (inj₂ ¬a) ¬¬a = ⊥-elim (¬¬a ¬a)

-- incomplete (no time!)

--------------------------------------------------------------------------------

-- exercise [Stable] (stretch)

-- say that a formula is stable if double negation elimination holds for it

Stable : Set → Set
Stable A = ¬ ¬ A → A

-- show that any negated formula is stable, and that the conjunction of two
-- stable formulas is stable

-- any negated formula is stable:
¬A-stable : ∀ {A : Set} → Stable (¬ A)
¬A-stable ¬¬¬a a = ¬¬¬a λ ¬a → ¬a a

-- the conjunction of two stable formulas is stable:
{-
×-stable : ∀ {A B : Set} → Stable (Stable A × Stable B)
×-stable ¬¬[sa×sb] = ⟨ (λ ¬¬a → {!!}) , (λ ¬¬b → {!!}) ⟩
-}

-- ??

--------------------------------------------------------------------------------
--
-- Quantifiers
-- 
--------------------------------------------------------------------------------

-- exercise [∀-distrib-×] (recommended)

-- show that universals distribute over conjunction

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)

∀-distrib-× = record
  { to      = λ a→Ba×Ca → ⟨ proj₁ ∘ a→Ba×Ca , proj₂ ∘ a→Ba×Ca ⟩
  ; from    = λ{ ⟨ a→Ba , a→Ca ⟩ a → ⟨ a→Ba a , a→Ca a ⟩ }
  ; from∘to = λ _ → refl
  ; to∘from = λ _ → refl
  }

-- compare this with the result (→-distrib-×) in chapter [connectives]

-- →-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)

{- 
  It looks like a specialization of the same property.
  I would like to be able to define a [∀-distrib-×′] using [→-distrib-×], as in:

    ∀-distrib-×′ {A} {B} {C} = →-distrib-× {∀ (x : A)} {B x} {C x}

  But I can't do that, because of [x], which is not in scope.
  I don't know if it's possible to write something like that in Agda.
-}

--------------------------------------------------------------------------------

-- exercise [⊎∀-implies-∀⊎]

-- show that a disjunction of universals implies a universal of disjunctions

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) →  ∀ (x : A) → B x ⊎ C x

⊎∀-implies-∀⊎ (inj₁ a→Ba) = inj₁ ∘ a→Ba
⊎∀-implies-∀⊎ (inj₂ a→Ca) = inj₂ ∘ a→Ca

-- does the converse hold?
-- if so, prove; if not, explain why

postulate
  ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)

{-
  I think the converse holds, but I can't prove it.
  I don't know why the following definition fails to compile:

    ∀⊎-implies-⊎∀ a→Ba⊎Ca = inj₁ λ a → inj₁ (a→Ba⊎Ca a)

  I believe it has something to do with the fact that, since Agda is
    intuitionistic, and we don't know which side of the ⊎ is true given
    any [x], this definition is insufficient.
-}

--------------------------------------------------------------------------------

-- exercise [∃-distrib-⊎] (recommended)

-- show that existentials distribute over disjunction

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)

∃-distrib-⊎ = record
  { to      = λ
    { ⟨ a , inj₁ Ba ⟩ → inj₁ ⟨ a , Ba ⟩
    ; ⟨ a , inj₂ Ca ⟩ → inj₂ ⟨ a , Ca ⟩
    }
  ; from    = λ
    { (inj₁ ⟨ a , Ba ⟩) → ⟨ a , (inj₁ Ba) ⟩
    ; (inj₂ ⟨ a , Ca ⟩) → ⟨ a , (inj₂ Ca) ⟩
    }
  ; from∘to = λ
    { ⟨ a , inj₁ Ba ⟩ → refl
    ; ⟨ a , inj₂ Ca ⟩ → refl
    }
  ; to∘from = λ
    { (inj₁ ⟨ a , Ba ⟩) → refl
    ; (inj₂ ⟨ a , Ca ⟩) → refl
    }
  }

--------------------------------------------------------------------------------

-- exercise [∃×-implies-×∃]

-- show that an existential of conjunctions
-- implies a conjunction of existentials

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)

∃×-implies-×∃ ⟨ a , ⟨ Ba , Ca ⟩ ⟩ = ⟨ ⟨ a , Ba ⟩ , ⟨ a , Ca ⟩ ⟩

-- does the converse hold?
-- if so, prove; if not, explain why

{-
  ×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} →
   (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)
-}

-- does not hold
-- x₁ from the first ∃ (B x₁) can be different from x₂ from the second ∃ (C x₂)

--------------------------------------------------------------------------------

-- exercise [∃-even-odd]

-- skipped

--------------------------------------------------------------------------------

-- exercise [∃-+-≤]

-- show that y ≤ z holds if and only if there exists a x such that x + y ≡ z

-- to
∃-+-≤-to : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-+-≤-to ⟨ zero , refl ⟩ = a≤a
  where
    a≤a : ∀ {a : ℕ} → a ≤ a
    a≤a {zero} = z≤n
    a≤a {suc _} = s≤s (a≤a)
∃-+-≤-to ⟨ suc _ , refl ⟩ = a≤b+a
  where
    a≤b+a : ∀ {a b : ℕ} → a ≤ b + a
    a≤b+a {zero} {b} = z≤n
    a≤b+a {suc a} {b} rewrite +-comm b (suc a) | +-comm a b  = s≤s a≤b+a

-- from
∃-+-≤-from : ∀ {y z : ℕ} → y ≤ z → ∃[ x ] (x + y ≡ z)
∃-+-≤-from {zero} {z} z≤n = ⟨ z , +-identityʳ z ⟩
∃-+-≤-from {suc y} {suc z} (s≤s y≤z) with ∃-+-≤-from y≤z
... | ⟨ x , refl ⟩ = ⟨ x , +-suc x y ⟩

--------------------------------------------------------------------------------

-- exercise [∃¬-implies-¬∀] (recommended)

-- show that existential of a negation implies negation of a universal

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set} → ∃[ x ] (¬ B x) → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ a , ¬Ba ⟩ = λ a→Ba → ¬Ba (a→Ba a)

-- does the converse hold?
-- if so, prove; if not, explain why

{-
  ¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set} → ¬ (∀ x → B x) → ∃[ x ] (¬ B x)
  ¬∀-implies-∃¬ ¬[a→Ba] = ⟨ {!!} , {!!} ⟩
-}

{-
  Can't prove, because despite knowing for all x that B x is false, an x can't
  be provided to build the ∃[ x ].
-}

--------------------------------------------------------------------------------

-- exercise [Bin-isomorphism] (stretch)

-- establish that there is an isomorphism between ℕ and ∃[ x ](Can x)

{-
ℕ≃∃Can : ℕ ≃ ∃[ x ](Bin.Can x)
ℕ≃∃Can = record
  { to      = λ n → ⟨ Bin.to n , Bin.can∘to {n} ⟩
  ; from    = λ{ ⟨ b , cb ⟩ → Bin.from b }
  ; from∘to = Bin.from∘to≡id
  ; to∘from = λ{ ⟨ b , cb ⟩ → begin
      ⟨ to ((λ { ⟨ b , cb ⟩ → from b }) ⟨ b , cb ⟩) , Bin.can∘to ⟩  ≡⟨⟩
      ⟨ Bin.to (Bin.from b) , Bin.can∘to ⟩                          ≡⟨⟩
      ⟨ b , cb ⟩                                                    ∎
    }
  }
-}

-- incomplete

-- don't know how to prove ⟨ Bin.to (Bin.from b) , cb ⟩ ≡ ⟨ b , cb ⟩

-- even though I have:
--   can-to∘from≡id : ∀ {b : Bin} → Can b → to (from b) ≡ b

-- how to write that ≡ in agda?

--------------------------------------------------------------------------------
--
-- Decidable
-- 
--------------------------------------------------------------------------------

-- exercise [_<?_] (recommended)

¬z<z : ¬ zero < zero
¬z<z ()

¬s<z : ∀ {m : ℕ} → ¬ suc m < zero
¬s<z {zero} ()
¬s<z {suc m} ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n 

-- define a function to decide strict inequality

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no ¬z<z
zero <? suc _ = yes z<s
suc m <? zero = no ¬s<z
suc m <? suc n with m <? n
... | yes m<n = yes (s<s m<n)
... | no ¬m<n = no (¬s<s ¬m<n)

--------------------------------------------------------------------------------

-- exercise [_≡ℕ?_]

-- define a function to decide whether two naturals are equal

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no λ()
suc m ≡ℕ? zero = no λ()
suc m ≡ℕ? suc n with m ≡ℕ? n
... | yes refl = yes refl
... | no ¬m≡n = no (λ{ refl → ¬m≡n refl })

--------------------------------------------------------------------------------

-- exercise [erasure]

-- skipped

--------------------------------------------------------------------------------

-- exercise [iff-erasure] (recommended)

_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ false  =  true
true  ⊃ false  =  false

-- give analogues of the _⇔_ operation from Chapter Isomorphism, operation
-- on booleans and decidables, and also show the corresponding erasure

-- 1
_iff_ : Bool → Bool → Bool
a iff b = (a ⊃ b) ∧ (b ⊃ a)

-- 2
_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes a ⇔-dec yes b = yes (record
  { to   = λ a → b
  ; from = λ b → a
  })
yes a ⇔-dec no ¬b = no λ a⇔b → ¬b (_⇔_.to a⇔b a)
no ¬a ⇔-dec yes b = no λ a⇔b → ¬a (_⇔_.from a⇔b b)
no ¬a ⇔-dec no ¬b = yes (record
  { to   = λ a → ⊥-elim (¬a a)
  ; from = λ b → ⊥-elim (¬b b)
  })

-- 3
iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes a) (yes b) = refl
iff-⇔ (yes a) (no ¬b) = refl
iff-⇔ (no ¬a) (yes b) = refl
iff-⇔ (no ¬a) (no ¬b) = refl

--------------------------------------------------------------------------------
--
-- Lists
-- 
--------------------------------------------------------------------------------

-- exercise [reverse-++-commute] (recommended)

-- show that the reverse of one list appended to another is the reverse
-- of the second appended to the reverse of the first

reverse-++-commute : ∀ {A : Set} {xs ys : List A} →
  reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

reverse-++-commute {_} {[]} {ys} rewrite ++-identityʳ (reverse ys) = refl
reverse-++-commute {_} {x ∷ xs} {ys}
  rewrite reverse-++-commute {_} {xs} {ys}
        | ++-assoc (reverse ys) (reverse xs) ([ x ])
        = refl

--------------------------------------------------------------------------------

-- exercise [reverse-involutive] (recommended)

-- a function is an involution if when applied
-- twice it acts as the identity function

-- show that reverse is an involution

reverse-involutive : ∀ {A : Set} {xs : List A} → reverse (reverse xs) ≡ xs
reverse-involutive {_} {[]} = refl
reverse-involutive {_} {x ∷ xs}
  rewrite reverse-++-commute {_} {reverse xs} {x ∷ []}
        | reverse-involutive {_} {xs}
        = refl

--------------------------------------------------------------------------------

-- exercise [map-compose]

-- prove that the map of a composition is equal to the composition of two maps

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C} →
  map (g ∘ f) ≡ map g ∘ map f

map-compose {_} {_} {_} {f} {g} = extensionality helper
  where
    helper : ∀ {A B C : Set} {f : A → B} {g : B → C} →
      ∀ (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    helper [] = refl
    helper {_} {_} {_} {f} {g} (x ∷ xs)
      rewrite helper {_} {_} {_} {f} {g} xs = refl

--------------------------------------------------------------------------------

-- exercise [map-++-commute]

-- prove the following relationship between map and append

map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A} →
  map f (xs ++ ys) ≡ map f xs ++ map f ys

map-++-commute {_} {_} {f} {[]} {ys} = refl
map-++-commute {_} {_} {f} {x ∷ xs} {ys}
  rewrite map-++-commute {_} {_} {f} {xs} {ys} = refl

--------------------------------------------------------------------------------

-- exercise [map-Tree]

-- define a type of trees with leaves of type A and internal nodes of type B

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

-- define a suitable map operator over trees

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f _ (leaf a) = leaf (f a)
map-Tree f g (node l b r) = node (map-Tree f g l) (g b) (map-Tree f g r)

--------------------------------------------------------------------------------

-- exercise [product] (recommended)

-- use fold to define a function to find the product of a list of numbers

-- for example: product [ 1 , 2 , 3 , 4 ] ≡ 24

product : List ℕ → ℕ
product = foldr _*_ 1

--------------------------------------------------------------------------------

-- exercise [foldr-++] (recommended)

-- show that fold and append are related as follows

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys rewrite foldr-++ _⊗_ e xs ys = refl

--------------------------------------------------------------------------------

-- exercise [map-is-foldr]

-- show that map can be defined using fold

map-is-foldr : ∀ {A B : Set} {f : A → B} → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {_} {_} {f} = extensionality helper
  where
    helper : ∀ {A B : Set} {f : A → B} →
      (ys : List A) → map f ys ≡ foldr (λ x xs → f x ∷ xs) [] ys
    helper {_} {_} {f} [] = refl
    helper {_} {_} {f} (y ∷ ys) rewrite helper {_} {_} {f} ys = refl

--------------------------------------------------------------------------------

-- exercise [fold-Tree]

-- define a suitable fold function for the type of trees given earlier

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree l⊗ n⊗ (leaf a) = l⊗ a
fold-Tree l⊗ n⊗ (node l b r) = n⊗ (fold-Tree l⊗ n⊗ l) b (fold-Tree l⊗ n⊗ r)

--------------------------------------------------------------------------------

-- exercise [map-is-fold-Tree]

-- skipped

--------------------------------------------------------------------------------

-- exercise [sum-downFrom] (stretch)

-- skipped

--------------------------------------------------------------------------------

-- exercise [foldl]

-- define a function foldl which is analogous to foldr, but where operations
-- associate to the left rather than the right

-- for example:
--   foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
--   foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ b []       = b
foldl _⊗_ b (a ∷ as) = foldl _⊗_ (b ⊗ a) as

--------------------------------------------------------------------------------

-- exercise [foldr-monoid-foldl]

-- skipped

--------------------------------------------------------------------------------

-- exercise [Any-++-⇔] (recommended)

-- prove a result similar to All-++-⇔, but with Any in place of All, and a
-- suitable replacement for _×_

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)

Any-++-⇔ xs ys =
  record
    { to   = to xs ys
    ; from = from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] ys AnyPys = inj₂ AnyPys
    to (x ∷ xs) ys (here Px) = inj₁ (here Px)
    to (x ∷ xs) ys (there AnyP[xs++ys]) with to xs ys AnyP[xs++ys]
    ... | inj₁ AnyPxs = inj₁ (there AnyPxs)
    ... | inj₂ AnyPys = inj₂ AnyPys

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
    from [] [] = case-⊎ id id
    from [] (y ∷ ys) (inj₁ ())
    from [] (y ∷ ys) (inj₂ AnyP[y∷ys]) = AnyP[y∷ys]
    from (x ∷ xs) [] (inj₁ AnyP[x∷xs]) rewrite ++-identityʳ xs = AnyP[x∷xs]
    from (x ∷ xs) [] (inj₂ ())
    from (x ∷ xs) (y ∷ ys) (inj₁ (here Px)) = here Px
    from (x ∷ xs) r@(y ∷ ys) (inj₁ (there AnyPxs)) =
      there (from xs r (inj₁ AnyPxs))
    from (x ∷ xs) r@(y ∷ ys) (inj₂ (here Py)) =
      there (from xs r (inj₂ (here Py)))
    from (x ∷ xs) r@(y ∷ ys) (inj₂ (there AnyPys)) =
      there (from xs r (inj₂ (there AnyPys)))

-- as a consequence, demonstrate an equivalence relating _∈_ and _++_

∈-++ : ∀ {A : Set} (a : A) (xs ys : List A) → (a ∈ xs ++ ys) ⇔ (a ∈ xs ⊎ a ∈ ys)
∈-++ _ = Any-++-⇔

--------------------------------------------------------------------------------

-- exercise [All-++-≃] (stretch)
-- exercise [¬Any≃All¬] (stretch)
-- exercise [any?] (stretch)
-- exercise [filter?] (stretch)

-- skipped (no time!)

\end{code}
