\begin{code}

-- defining equality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

--------------------------------------------------------------------------------

-- equality is an equivalence relation
-- reflexive, symmetric, and transitive

-- reflexive by construction

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

--------------------------------------------------------------------------------

-- congruence and substitution

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
  → f u v ≡ f x y
cong₂ f refl refl = refl 

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst _ refl Px = Px

--------------------------------------------------------------------------------

-- chains of equations

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _ ∎ = refl

open ≡-Reasoning

--------------------------------------------------------------------------------

-- definitions

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

infixl 6 _+_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n   : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

--------------------------------------------------------------------------------

-- exercise [≤-Reasoning] (stretch)

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
    where postulate ≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
      
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
      postulate +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-begin
  m + p  ≤⟨ +-monoˡ-≤ m≤n ⟩
  n + p  ≤⟨ +-monoʳ-≤ p≤q ⟩
  n + q  ≤-∎

\end{code}
