\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import 5-isomorphism using (_≃_; extensionality)

--------------------------------------------------------------------------------

-- negation

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

¬¬-intro′ : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

--------------------------------------------------------------------------------

open import 3-relations using (_<_)

open _<_

-- exercise [<-irreflexive] (recommended)

-- using negation, show that strict inequality is irreflexive, that is, n < n
--   holds for no n

<-irreflexive : ∀ {x : ℕ} → ¬ (x < x)
<-irreflexive (s<s x<x) = <-irreflexive x<x

--------------------------------------------------------------------------------

-- exercise [trichotomy]

-- show that strict inequality satisfies trichotomy, that is, for any
--   naturals m and n exactly one of the following holds

{-
record Tri (m n : ℕ) : Set where
  field
    tri-< : m < n →   (m ≢ n) × (¬ n < m) 
    tri-≡ : m ≡ n → ¬ m < n × ¬ n < m 
    tri-> : n < m → ¬ m < n ×   m ≢ n 

<-tri : ∀ (m n : ℕ) → Tri m n
<-tri m n = record
  { tri-< = λ m<n → {!!} Data.Product., λ n<m → {!tri->!}
  ; tri-≡ = {!!}
  ; tri-> = {!!}
  }
-}

{-
data Trichotomy (m n : ℕ) : Set where
  <-tri-< : m < n → Trichotomy m n
  <-tri-≡ : m ≡ n → Trichotomy m n
  <-tri-> : n < m → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = <-tri-≡ refl
<-trichotomy zero (suc n) = <-tri-< z<s
<-trichotomy (suc m) zero = <-tri-> z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
... | <-tri-< m<n = <-tri-< (s<s m<n)
... | <-tri-≡ m≡n = <-tri-≡ (cong suc m≡n)
... | <-tri-> m>n = <-tri-> (s<s m>n)
-}

--------------------------------------------------------------------------------

-- exercise [⊎-dual-×] (recommended)

postulate →-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

{-
⊎-dual-× = record
  { to      = λ ¬[a⊎b] → ⟨ (λ a → ¬[a⊎b] (inj₁ a)) , (λ b → ¬[a⊎b] (inj₂ b)) ⟩
  ; from    = λ
    { ⟨ ¬a , ¬b ⟩ (inj₁ a) → ¬a a
    ; ⟨ ¬a , ¬b ⟩ (inj₂ b) → ¬b b
    }
  ; from∘to = λ ¬[a⊎b] → extensionality λ
    { (inj₁ a) → refl
    ; (inj₂ b) → refl
    }
  ; to∘from = λ _ → refl
  }
-}

-- do we also have the following?
-- ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)

{- 
no, because we can't prove the [to], as in:
  ×-dual-⊎-to : ∀ {A B : Set} → ¬ (A × B) → (¬ A) ⊎ (¬ B)

for the same reasons we can't prove ¬¬A → A

but we can prove the [from]
-}

×-dual-⊎-from : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎-from (inj₁ ¬a) a×b = ¬a (proj₁ a×b)
×-dual-⊎-from (inj₂ ¬b) a×b = ¬b (proj₂ a×b)

--------------------------------------------------------------------------------

-- excluded middle is irrefutable

postulate em : ∀ {A : Set} → A ⊎ ¬ A
em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable ¬[a⊎¬a] = ¬[a⊎¬a] (inj₂ λ a → ¬[a⊎¬a] (inj₁ a))

--------------------------------------------------------------------------------

-- exercise [classical] (stretch)

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

{-
dne→pl : ∀ {A B : Set} → (¬ ¬ A → A) → (((A → B) → A) → A)
-- dne→pl ¬¬a→a [a→b]→a = ¬¬a→a λ ¬a → {!!}
dne→pl ¬¬a→a [a→b]→a = [a→b]→a λ a → ⊥-elim {!¬¬a→a!}
-}

--------------------------------------------------------------------------------

-- exercise [stable] (stretch)

-- say that a formula is stable if double negation elimination holds for it

Stable : Set → Set
Stable A = ¬ ¬ A → A

-- show that any negated formula is stable, and that the conjunction of two
-- stable formulas is stable

-- any negated formula is stable:
¬A-is-stable : ∀ {A : Set} → Stable (¬ A)
¬A-is-stable ¬¬¬a a = ¬¬¬a λ ¬a → ¬a a

-- the conjunction of two stable formulas is stable:
{-
⊎-stable : ∀ {A B : Set} → Stable (Stable A ⊎ Stable B)
⊎-stable ¬¬[sa⊎sb] = { }0
-}

\end{code}
