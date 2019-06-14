\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z  : ∀ {Γ A}           → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

data _⊢_ : Context → Type → Set where
  `_    : ∀ {Γ} {A}   → Γ ∋ A → Γ ⊢ A
  ƛ_    : ∀ {Γ} {A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_   : ∀ {Γ} {A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  `zero : ∀ {Γ}       → Γ ⊢ `ℕ
  `suc_ : ∀ {Γ}       → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case  : ∀ {Γ A}     → Γ ⊢ `ℕ → Γ ⊢ A → Γ , `ℕ ⊢ A → Γ ⊢ A
  μ_    : ∀ {Γ A}     → Γ , A ⊢ A → Γ ⊢ A

lookup : Context → ℕ → Type
lookup (Γ , A) zero    = A
lookup (Γ , _) (suc n) = lookup Γ n
lookup ∅       _       = ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero    = Z
count {Γ , _} (suc n) = S (count n)
count {∅}     _       = ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n = ` count n

--------------------------------------------------------------------------------

two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two

Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

--------------------------------------------------------------------------------

-- exercise [mul] (recommended)

mul : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
mul = μ ƛ ƛ (case (# 1) (`zero) (plus · # 1 · (# 3 · # 0 · # 1)))

--------------------------------------------------------------------------------

ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z     = Z
ext ρ (S x) = S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)        = ` (ρ x)
rename ρ (ƛ N)        = ƛ (rename (ext ρ) N)
rename ρ (L · M)      = (rename ρ L) · (rename ρ M)
rename ρ (`zero)      = `zero
rename ρ (`suc M)     = `suc (rename ρ M)
rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)        = μ (rename (ext ρ) N)

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z     = ` Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)        = σ k
subst σ (ƛ N)        = ƛ (subst (exts σ) N)
subst σ (L · M)      = (subst σ L) · (subst σ M)
subst σ (`zero)      = `zero
subst σ (`suc M)     = `suc (subst σ M)
subst σ (case L M N) = case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)        = μ (subst (exts σ) N)

_[_] : ∀ {Γ A B} → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
    σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
    σ Z     = M
    σ (S x) = ` x

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → Value (ƛ N)

  V-zero : ∀ {Γ}
    → Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
    → Value (`suc V)

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      -------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      ----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      --------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      -----------------------------
    → case (`suc V) M N —→ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ---------------
    → μ N —→ N [ μ N ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {Γ} {A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      -------------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                          =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                 =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                    =  step (β-ƛ VM)
progress (`zero)                        =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                     =  step (ξ-suc M—→M′)
...    | done VM                        =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                     =  step (ξ-case L—→L′)
...    | done V-zero                    =  step (β-zero)
...    | done (V-suc VL)                =  step (β-suc VL)
progress (μ N)                          =  step (β-μ)

data Gas : Set where
  gas : ℕ → Gas

data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N

data Steps : ∀ {A} → ∅ ⊢ A → Set where

  steps : ∀ {A} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

--------------------------------------------------------------------------------

-- exercise [mul-example] (recommended)

-- using the evaluator, confirm that two times two is four

2*2 : ∀ {Γ} → Γ ⊢ `ℕ
2*2 = mul · two · two

-- eval (gas 100) (mul · two · two)

{-

steps
((μ
  (ƛ
   (ƛ
    case (` (S Z)) `zero
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` (S Z)
     · (` (S (S (S Z))) · ` Z · ` (S Z))))))
 · `suc (`suc `zero)
 · `suc (`suc `zero)
 —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
 (ƛ
  (ƛ
   case (` (S Z)) `zero
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` (S Z)
    ·
    ((μ
      (ƛ
       (ƛ
        case (` (S Z)) `zero
        ((μ
          (ƛ
           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
         · ` (S Z)
         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z)))))
 · `suc (`suc `zero)
 · `suc (`suc `zero)
 —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
 (ƛ
  case (`suc (`suc `zero)) `zero
  ((μ
    (ƛ
     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · ` (S Z)
   ·
   ((μ
     (ƛ
      (ƛ
       case (` (S Z)) `zero
       ((μ
         (ƛ
          (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
        · ` (S Z)
        · (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 · `suc (`suc `zero)
 —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
 case (`suc (`suc `zero)) `zero
 ((μ
   (ƛ
    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  · `suc (`suc `zero)
  ·
  ((μ
    (ƛ
     (ƛ
      case (` (S Z)) `zero
      ((μ
        (ƛ
         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` (S Z)
       · (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · ` Z
   · `suc (`suc `zero)))
 —→⟨ β-suc (V-suc V-zero) ⟩
 (μ
  (ƛ
   (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
 · `suc (`suc `zero)
 ·
 ((μ
   (ƛ
    (ƛ
     case (` (S Z)) `zero
     ((μ
       (ƛ
        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` (S Z)
      · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
 (ƛ
  (ƛ
   case (` (S Z)) (` Z)
   (`suc
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z)))))
 · `suc (`suc `zero)
 ·
 ((μ
   (ƛ
    (ƛ
     case (` (S Z)) `zero
     ((μ
       (ƛ
        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` (S Z)
      · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((μ
   (ƛ
    (ƛ
     case (` (S Z)) `zero
     ((μ
       (ƛ
        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` (S Z)
      · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((ƛ
   (ƛ
    case (` (S Z)) `zero
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` (S Z)
     ·
     ((μ
       (ƛ
        (ƛ
         case (` (S Z)) `zero
         ((μ
           (ƛ
            (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
          · ` (S Z)
          · (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · ` (S Z)))))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((ƛ
   case (`suc `zero) `zero
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` (S Z)
    ·
    ((μ
      (ƛ
       (ƛ
        case (` (S Z)) `zero
        ((μ
          (ƛ
           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
         · ` (S Z)
         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z))))
  · `suc (`suc `zero))
 —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 case (`suc `zero) `zero
 ((μ
   (ƛ
    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  · `suc (`suc `zero)
  ·
  ((μ
    (ƛ
     (ƛ
      case (` (S Z)) `zero
      ((μ
        (ƛ
         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` (S Z)
       · (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · ` Z
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((μ
   (ƛ
    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  · `suc (`suc `zero)
  ·
  ((μ
    (ƛ
     (ƛ
      case (` (S Z)) `zero
      ((μ
        (ƛ
         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` (S Z)
       · (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((ƛ
   (ƛ
    case (` (S Z)) (` Z)
    (`suc
     ((μ
       (ƛ
        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · ` (S Z)))))
  · `suc (`suc `zero)
  ·
  ((μ
    (ƛ
     (ƛ
      case (` (S Z)) `zero
      ((μ
        (ƛ
         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` (S Z)
       · (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((ƛ
   case (`suc (`suc `zero)) (` Z)
   (`suc
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z))))
  ·
  ((μ
    (ƛ
     (ƛ
      case (` (S Z)) `zero
      ((μ
        (ƛ
         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` (S Z)
       · (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((ƛ
   case (`suc (`suc `zero)) (` Z)
   (`suc
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z))))
  ·
  ((ƛ
    (ƛ
     case (` (S Z)) `zero
     ((μ
       (ƛ
        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` (S Z)
      ·
      ((μ
        (ƛ
         (ƛ
          case (` (S Z)) `zero
          ((μ
            (ƛ
             (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
           · ` (S Z)
           · (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` Z
       · ` (S Z)))))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((ƛ
   case (`suc (`suc `zero)) (` Z)
   (`suc
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z))))
  ·
  ((ƛ
    case `zero `zero
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` (S Z)
     ·
     ((μ
       (ƛ
        (ƛ
         case (` (S Z)) `zero
         ((μ
           (ƛ
            (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
          · ` (S Z)
          · (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · ` (S Z))))
   · `suc (`suc `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((ƛ
   case (`suc (`suc `zero)) (` Z)
   (`suc
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z))))
  ·
  case `zero `zero
  ((μ
    (ƛ
     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · `suc (`suc `zero)
   ·
   ((μ
     (ƛ
      (ƛ
       case (` (S Z)) `zero
       ((μ
         (ƛ
          (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
        · ` (S Z)
        · (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · `suc (`suc `zero))))
 —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 ((ƛ
   case (`suc (`suc `zero)) (` Z)
   (`suc
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z))))
  · `zero)
 —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 case (`suc (`suc `zero)) `zero
 (`suc
  ((μ
    (ƛ
     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · ` Z
   · `zero))
 —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 `suc
 ((μ
   (ƛ
    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  · `suc `zero
  · `zero)
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 `suc
 ((ƛ
   (ƛ
    case (` (S Z)) (` Z)
    (`suc
     ((μ
       (ƛ
        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · ` (S Z)))))
  · `suc `zero
  · `zero)
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 `suc
 ((ƛ
   case (`suc `zero) (` Z)
   (`suc
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z))))
  · `zero)
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ V-zero)) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 `suc
 case (`suc `zero) `zero
 (`suc
  ((μ
    (ƛ
     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · ` Z
   · `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 `suc
 (`suc
  ((μ
    (ƛ
     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · `zero
   · `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 `suc
 (`suc
  ((ƛ
    (ƛ
     case (` (S Z)) (` Z)
     (`suc
      ((μ
        (ƛ
         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` Z
       · ` (S Z)))))
   · `zero
   · `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 `suc
 (`suc
  ((ƛ
    case `zero (` Z)
    (`suc
     ((μ
       (ƛ
        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · ` (S Z))))
   · `zero))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ V-zero))) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 ·
 `suc
 (`suc
  case `zero `zero
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · `zero)))
 —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
 (ƛ
  case (`suc (`suc `zero)) (` Z)
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · ` (S Z))))
 · `suc (`suc `zero)
 —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
 case (`suc (`suc `zero)) (`suc (`suc `zero))
 (`suc
  ((μ
    (ƛ
     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · ` Z
   · `suc (`suc `zero)))
 —→⟨ β-suc (V-suc V-zero) ⟩
 `suc
 ((μ
   (ƛ
    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
 `suc
 ((ƛ
   (ƛ
    case (` (S Z)) (` Z)
    (`suc
     ((μ
       (ƛ
        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · ` (S Z)))))
  · `suc `zero
  · `suc (`suc `zero))
 —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
 `suc
 ((ƛ
   case (`suc `zero) (` Z)
   (`suc
    ((μ
      (ƛ
       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
     · ` Z
     · ` (S Z))))
  · `suc (`suc `zero))
 —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
 `suc
 case (`suc `zero) (`suc (`suc `zero))
 (`suc
  ((μ
    (ƛ
     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · ` Z
   · `suc (`suc `zero)))
 —→⟨ ξ-suc (β-suc V-zero) ⟩
 `suc
 (`suc
  ((μ
    (ƛ
     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
 `suc
 (`suc
  ((ƛ
    (ƛ
     case (` (S Z)) (` Z)
     (`suc
      ((μ
        (ƛ
         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
       · ` Z
       · ` (S Z)))))
   · `zero
   · `suc (`suc `zero)))
 —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
 `suc
 (`suc
  ((ƛ
    case `zero (` Z)
    (`suc
     ((μ
       (ƛ
        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
      · ` Z
      · ` (S Z))))
   · `suc (`suc `zero)))
 —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
 `suc
 (`suc
  case `zero (`suc (`suc `zero))
  (`suc
   ((μ
     (ƛ
      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
    · ` Z
    · `suc (`suc `zero))))
 —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
(done (V-suc (V-suc (V-suc (V-suc V-zero)))))

-}

--------------------------------------------------------------------------------



\end{code}
