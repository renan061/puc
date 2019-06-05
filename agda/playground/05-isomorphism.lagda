\begin{code}

module 5-isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc)

-- emacs: C-u 80 -

--------------------------------------------------------------------------------

-- function composition

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

--------------------------------------------------------------------------------

-- extensionality

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m zero rewrite +-comm m zero = refl
same-app m (suc n) rewrite +-comm m (suc n) | +-comm n m | same-app m n = refl

same : _+′_ ≡ _+_
same = extensionality λ m → extensionality λ n → same-app m n

--------------------------------------------------------------------------------

-- isomorphism

infix 0 _≃_

record _≃_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl = record
  { to = λ x → x
  ; from = λ y → y
  ; from∘to = λ x → refl
  ; to∘from = λ y → refl
  }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B = record
  { to = from A≃B
  ; from = to A≃B
  ; from∘to = to∘from A≃B
  ; to∘from = from∘to A≃B
  }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C = record
  { to = to B≃C ∘ to A≃B
  ; from = from A≃B ∘ from B≃C
  ; from∘to = λ x →
      begin
        from A≃B (from B≃C (to B≃C (to A≃B x)))
      ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
        from A≃B (to A≃B x)
      ≡⟨ from∘to A≃B x ⟩
        x
      ∎
  ; to∘from = λ y →
      begin
        to B≃C (to A≃B (from A≃B (from B≃C y)))
      ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
        to B≃C (from B≃C y)
      ≡⟨ to∘from B≃C y ⟩
        y
      ∎
  } 

--------------------------------------------------------------------------------

-- equational reasoning for isomorphism

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

--------------------------------------------------------------------------------

-- embedding

infix 0 _≲_

record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

open _≲_

-- same as before
postulate 
  ≲-refl : ∀ {A : Set} → A ≲ A
  ≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → to A≲B ≡ from B≲A
  → from A≲B ≡ to B≲A
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to = record
  { to = to A≲B
  ; from = from A≲B
  ; from∘to = from∘to A≲B
  ; to∘from = λ y → begin
      to A≲B (from A≲B y)  ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
      to A≲B (to B≲A y)    ≡⟨ cong-app to≡from (to B≲A y) ⟩
      from B≲A (to B≲A y)  ≡⟨ from∘to B≲A y ⟩
      y                    ∎
  }

--------------------------------------------------------------------------------

-- equational reasoning for embedding

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set} → A ≲ B → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set) → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

--------------------------------------------------------------------------------

-- exercise [≃-implies-≲]

-- show that every isomorphism implies an embedding

≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B = record
  { to = λ x → to A≃B x
  ; from = λ x → from A≃B x
  ; from∘to = λ x → from∘to A≃B x
  }

--------------------------------------------------------------------------------

-- exercise [_⇔_] (recommended)

-- define a equivalence of propositions (also known as “if and only if”)

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _⇔_

-- show that equivalence is reflexive, symmetric, and transitive

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = record
  { to = λ x → x
  ; from = λ x → x
  }

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B = record
  { to = from A⇔B
  ; from = to A⇔B
  }

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C  → A ⇔ C
⇔-trans A⇔B B⇔C = record
  { to = to B⇔C ∘ to A⇔B
  ; from = from A⇔B ∘ from B⇔C
  }

--------------------------------------------------------------------------------

-- exercise [Bin-embedding] (stretch)

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

  from-inc≡suc-from : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
  from-inc≡suc-from nil = refl
  from-inc≡suc-from (x0 x) = refl
  from-inc≡suc-from (x1 x) rewrite
    from-inc≡suc-from x | +-suc (from x) (from x) = refl

  from-to≡id : ∀ (n : ℕ) → from (to n) ≡ n
  from-to≡id zero = refl
  from-to≡id (suc n) rewrite from-inc≡suc-from (to n) | from-to≡id n = refl

-- establish that there is an embedding of ℕ into Bin

ℕ-≲-Bin : ℕ ≲ Bin
ℕ-≲-Bin = record
  { to      = Bin.to
  ; from    = Bin.from
  ; from∘to = Bin.from-to≡id
  }

-- why is there not an isomorphism?

-- because of the leading-zero alternative representations for binaries

--------------------------------------------------------------------------------

\end{code}
