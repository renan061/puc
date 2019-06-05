\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import 5-isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open 5-isomorphism.≃-Reasoning
open 5-isomorphism._⇔_

--------------------------------------------------------------------------------

-- conjunction (and)

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , _ ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ _ , y ⟩ = y

-- alternative as record
record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ _ , _ ⟩ = refl

infixr 2 _×_

--------------------------------------------------------------------------------

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record
  { to      = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from    = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from∘to = λ{ ⟨ x , y ⟩ → refl }
  ; to∘from = λ{ ⟨ x , y ⟩ → refl }
  }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record
  { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩}
  ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩}
  ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
  ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
  }

--------------------------------------------------------------------------------

-- exercise [⇔≃×] (recommended)

-- show that A ⇔ B is isomorphic to (A → B) × (B → A)

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
  { to      = λ A⇔B → ⟨ to A⇔B , from A⇔B ⟩
  ; from    = λ{ ⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A }}
  ; from∘to = λ _ → refl
  ; to∘from = λ{ ⟨ _ , _ ⟩ → refl}
  }

--------------------------------------------------------------------------------

-- unit (truth)

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

×-⊤-identityᴸ : ∀ {A : Set} → ⊤ × A ≃ A
×-⊤-identityᴸ = record
  { to      = λ{ ⟨ tt , A ⟩ → A}
  ; from    = λ A → ⟨ tt , A ⟩
  ; from∘to = λ{ ⟨ tt , A ⟩ → refl}
  ; to∘from = λ A → refl
  }

×-⊤-identityᴿ : ∀ {A : Set} → (A × ⊤) ≃ A
×-⊤-identityᴿ {A} = ≃-begin
  (A × ⊤)  ≃⟨ ×-comm ⟩
  (⊤ × A)  ≃⟨ ×-⊤-identityᴸ ⟩
  A        ≃-∎

--------------------------------------------------------------------------------

-- disjunction (sum)

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infix 1 _⊎_

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ A→C _ (inj₁ A) = A→C A
case-⊎ _ B→C (inj₂ B) = B→C B

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ A) = refl
η-⊎ (inj₂ B) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ A) = refl
uniq-⊎ h (inj₂ B) = refl

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

-- empty (false)

data ⊥ : Set where
  -- empty

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

--------------------------------------------------------------------------------

-- exercise [⊥-identityᴸ] (recommended)

-- show empty is the left identity of sums up to isomorphism

⊎-⊥-identityᴸ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊎-⊥-identityᴸ = record
  { to      = λ{ (inj₁ ()) ; (inj₂ A) → A }
  ; from    = λ A → inj₂ A
  ; from∘to = λ{ (inj₁ ()) ; (inj₂ A) → refl }
  ; to∘from = λ A → refl
  }

--------------------------------------------------------------------------------

-- exercise [⊥-identityᴿ]

-- show empty is the right identity of sums up to isomorphism

⊎-⊥-identityᴿ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊎-⊥-identityᴿ {A} = ≃-begin
  (A ⊎ ⊥)  ≃⟨ ⊎-comm ⟩
  (⊥ ⊎ A)  ≃⟨ ⊎-⊥-identityᴸ ⟩
  A        ≃-∎

--------------------------------------------------------------------------------

-- function (implication)

→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim A→B A = A→B A

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying = record
  { to      = λ{ A→B→C ⟨ A , B ⟩ → A→B→C A B}
  ; from    = λ{ A×B→C A B → A×B→C ⟨ A , B ⟩}
  ; from∘to = λ A→B→C → refl
  ; to∘from = λ A×B→C → extensionality λ{ ⟨ A , B ⟩ → refl }
  }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = record
  { to      = λ A⊎B→C → ⟨ (λ A → A⊎B→C (inj₁ A)) , (λ B → A⊎B→C (inj₂ B)) ⟩
  ; from    = λ
    { ⟨ A→B , _ ⟩ (inj₁ A) → A→B A
    ; ⟨ _ , B→C ⟩ (inj₂ B) → B→C B
    }
  ; from∘to = λ{ A⊎B→C → extensionality λ{ (inj₁ A) → refl ; (inj₂ B) → refl}}
  ; to∘from = λ{ ⟨ A→C , B→C ⟩ → refl }
  }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = record
  { to      = λ a→b×c → ⟨ (λ a → proj₁ (a→b×c a)) , (λ a → proj₂ (a→b×c a)) ⟩
  ; from    = λ{ ⟨ a→b , a→c ⟩ a → ⟨ a→b a , a→c a ⟩ }
  ; from∘to = λ{ a→b×c → extensionality λ{ a → η-× (a→b×c a) }}
  ; to∘from = λ{ ⟨ a→b , a→c ⟩ → refl }
  }

--------------------------------------------------------------------------------

-- distribution

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = record
  { to      = λ
    { ⟨ inj₁ a , c ⟩ → inj₁ ⟨ a , c ⟩
    ; ⟨ inj₂ b , c ⟩ → inj₂ ⟨ b , c ⟩
    }
  ; from    = λ
    { (inj₁ ⟨ a , c ⟩) → ⟨ inj₁ a , c ⟩
    ; (inj₂ ⟨ b , c ⟩) → ⟨ inj₂ b , c ⟩
    }
  ; from∘to = λ
    { ⟨ inj₁ a , c ⟩ → refl
    ; ⟨ inj₂ b , c ⟩ → refl
    }
  ; to∘from = λ
    { (inj₁ ⟨ a , c ⟩) → refl
    ; (inj₂ ⟨ b , c ⟩) → refl
    }
  }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = record
    { to      = λ
      { (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
      ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
      }
    ; from    = λ
      { ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
      ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
      ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
      }
    ; from∘to = λ
      { (inj₁ ⟨ x , y ⟩) → refl
      ; (inj₂ z)         → refl
      }
    }

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

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- ×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- does not hold

-- counterexample:
--   A ≡ true
--   B ≡ false
--   C ≡ false
--   D ≡ true
--   (A ⊎ C) × (B ⊎ D) is true
--   (A × B) ⊎ (C × D) is false

\end{code}
