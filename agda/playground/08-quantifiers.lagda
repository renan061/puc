\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import 5-isomorphism using (_≃_; extensionality)

open import Data.Nat.Properties using (+-suc; +-comm; +-identityʳ)

--------------------------------------------------------------------------------

-- universals

∀-elim : ∀ {A : Set} {B : A → Set} → (L : ∀ (x : A) → B x) → (M : A) → B M
∀-elim L M = L M

--------------------------------------------------------------------------------

-- exercise [∀-distrib-×] (recommended)

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
  I think the converse holds, but I couldn't prove it.
  I don't know why the following definition fails to compile:

    ∀⊎-implies-⊎∀ a→Ba⊎Ca = inj₁ λ a → inj₁ (a→Ba⊎Ca a)

  I believe it has something to do with the fact that, since Agda is
    intuitionistic, and we don't know which side of the ⊎ is true given
    any [x], this definition is insufficient.
-}

--------------------------------------------------------------------------------

-- exercise [∀-×]

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- let B be a type indexed by Tri, that is B : Tri → Set
-- show that ∀ (x : Tri) → B x is isomorphic to B aa × B bb × B cc

-- error
-- t→Bt x != (λ { aa → t→Bt aa ; bb → t→Bt bb ; cc → t→Bt cc }) x

{-
∀-x : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-x = record
  { to      = λ t→Bt → ⟨ t→Bt aa , ⟨ t→Bt bb , t→Bt cc ⟩ ⟩
  ; from    = λ{ ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → λ{ aa → Baa ; bb → Bbb ; cc → Bcc } }
  ; from∘to = λ t→Bt → extensionality ?
  ; to∘from = λ _ → refl
  }
-}

--------------------------------------------------------------------------------

-- existentials

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- unbound domain
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- elim
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set} → (∀ x → B x → C) → ∃[ x ] B x → C
∃-elim f ⟨ x , y ⟩ = f x y

-- currying
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)

∀∃-currying = record
  { to      = ∃-elim
  ; from    = λ{ ∃xB→C a Ba → ∃xB→C ⟨ a , Ba ⟩ }
  ; from∘to = λ _ → refl
  ; to∘from = λ ∃xB→C → extensionality (λ{ ⟨ a , Bx ⟩ → refl })
  }

--------------------------------------------------------------------------------

-- exercise [∃-distrib-⊎] (recommended)

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

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)

∃×-implies-×∃ ⟨ a , ⟨ Ba , Ca ⟩ ⟩ = ⟨ ⟨ a , Ba ⟩ , ⟨ a , Ca ⟩ ⟩

-- does the converse hold?
-- if so, prove; if not, explain why

postulate
  ×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} →
   (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)

-- ×∃-implies-∃× ⟨ ⟨ a₁ , Ba₁ ⟩ , ⟨ a₂ , Ca₂ ⟩ ⟩ = ⟨ a₁ , ⟨ Ba₁ , {!!} ⟩ ⟩

-- does not hold
-- x₁ from the first ∃ can be different from x₂ from the second ∃

--------------------------------------------------------------------------------

-- exercise [∃-⊎]

-- TODO

--------------------------------------------------------------------------------

-- an existential example (odd & even)

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

-- forwards direction
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc e) with even-∃ e
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

-- backwards direction
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩ = even-zero
∃-even ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)

--------------------------------------------------------------------------------

-- exercise [∃-even-odd]

-- how do the proofs become more difficult if we replace m * 2 and 1 + m * 2 by
-- 2 * m and 2 * m + 1? Rewrite the proofs of ∃-even and ∃-odd when restated in
-- this way

-- TODO

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

-- existentials, universals, and negation

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set} →
  (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = record
  { to      = λ ¬∃B a Ba → ¬∃B ⟨ a , Ba ⟩
  ; from    = λ{ a→¬Ba ⟨ a , Ba ⟩ → a→¬Ba a Ba }
  ; from∘to = λ ¬∃B → extensionality λ{ ⟨ a , Ba ⟩ → refl }
  ; to∘from = λ a→¬Ba → refl
  }

--------------------------------------------------------------------------------

-- exercise [∃¬-implies-¬∀] (recommended)

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set} → ∃[ x ] (¬ B x) → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ a , ¬Ba ⟩ = λ a→Ba → ¬Ba (a→Ba a)

-- does the converse hold?
-- if so, prove; if not, explain why

postulate
  ¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set} → ¬ (∀ x → B x) → ∃[ x ] (¬ B x)
-- ¬∀-implies-∃¬ ¬[a→Ba] = ⟨ {!!} , {!!} ⟩

{-
  Can't prove, because despite knowing for all x that B x is false, an x can't
  be provided to build the ∃[ x ].
-}

--------------------------------------------------------------------------------

-- exercise [Bin-isomorphism] (stretch)

-- using the above, establish that there is an isomorphism
-- between ℕ and ∃[ x ](Can x)

open import bin using (Bin; to; from; from-to≡id; Can; can-to; can-to-from≡id)

aux : ∀ {A : Set} {B C : A → Set} → ∀ (x y : A) → x ≡ y → B ≡ C → ∃[ x ] B x ≡ ∃[ y ] C y
aux x .x refl refl = refl

{-
aux2 : ∀ {A : Set} {B C : A → Set} → (∃[ x ] B x ≡ ∃[ y ] C y) → (∃[ x ] (B x ≡ C x))
aux2 = ?
-}

-- to (from b) != b of type Bin

-- (y : ∃-syntax (λ x → Can x)) → ⟨ to ((λ { ⟨ b , cb ⟩ → from b }) y) , can-to ⟩ ≡ y
-- f : (y : ∃-syntax (λ x → Can x)) → ⟨ to ((λ { ⟨ b , cb ⟩ → from b }) y) , can-to ⟩ ≡ y

todo-to : ℕ → ∃[ x ](Can x)
todo-to n = ⟨ to n , can-to {n} ⟩

todo-from : ∃[ x ](Can x) → ℕ
todo-from ⟨ b , cb ⟩ = from b

teste : ∃[ x ](Can x) → Bin
teste ⟨ b , cb ⟩ = b -- COMO EU PEGO A PORRA TO CB?

todo : (e : ∃[ x ](Can x)) → todo-to (todo-from e) ≡ e
todo ⟨ b , cb ⟩ = {!!}

-- to-from≡id : ∀ {A B : Set} (t : A → B) (f : B → A) → ∃[ b ](Can b) (t (f b) ≡ b)
-- to-from≡id = {!!}

{-
ℕ≃∃Can : ℕ ≃ ∃[ x ](Can x)
ℕ≃∃Can = record
  { to      = λ n → ⟨ to n , can-to {n} ⟩
  ; from    = λ{ ⟨ b , cb ⟩ → from b }
  ; from∘to = from-to≡id
  ; to∘from = λ{ ⟨ b , cb ⟩ → begin
      ⟨ to ((λ { ⟨ b , cb ⟩ → from b }) ⟨ b , cb ⟩) , can-to ⟩  ≡⟨⟩
      ⟨ to (from b) , can-to ⟩                                  ≡⟨⟩
      ⟨ b , cb ⟩                                                ∎
    }
  }
-}

\end{code}
